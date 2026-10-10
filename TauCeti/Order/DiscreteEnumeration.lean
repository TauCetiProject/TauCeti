/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Order.SuccPred.LinearLocallyFinite
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Enumerating an unbounded, locally finite subset of a linear order

A subset `S` of a linear order which is *unbounded above* and has *finitely many elements below
every bound* is exactly a strictly increasing sequence: it is order-isomorphic to `ℕ`, and the
inverse isomorphism is a strictly monotone `f : ℕ → α` with `Set.range f = S`.

Mathlib enumerates subsets of `ℕ` (`Nat.nth`, `Nat.Subtype.orderIsoOfNat`) and has no statement
about subsets of a general linear order, or of `ℝ`.  It does, however, have every ingredient:
`LocallyFiniteOrder.ofFiniteIcc` turns "all closed intervals are finite" into a
`LocallyFiniteOrder` instance, `LinearLocallyFiniteOrder.succOrder`/`predOrder` turn that into a
`SuccOrder`/`PredOrder` with `IsSuccArchimedean` for free, and
`orderIsoNatOfLinearSuccPredArch` enumerates any such order that has a bottom and no top.  What
is added here is the translation of the two set-level hypotheses into those four instances on
the subtype `↥S`.

The two hypotheses are stated in the form a spectral argument produces them: `∀ b, ∃ x ∈ S,
b < x` is "unbounded above", and `∀ b, (S ∩ Set.Iic b).Finite` is "locally finite", which is how
a discreteness theorem for eigenvalues below a bound comes out.

## Main results

* `TauCeti.exists_isLeast_of_finite_inter_Iic`: every nonempty subset of a locally finite `S`
  has a least element -- the well-ordering hidden in the hypothesis.
* `TauCeti.nonempty_orderIso_nat_of_unbounded_of_finite_inter_Iic`: `↥S ≃o ℕ`.
* `TauCeti.exists_strictMono_range_eq_of_unbounded_of_finite_inter_Iic`: the strictly monotone
  enumeration `f : ℕ → α` with `Set.range f = S`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib.
-/

public section

namespace TauCeti

variable {α : Type*} [LinearOrder α] {S T : Set α}

/-- **A locally finite set is well-ordered.**  If `S` meets every `Set.Iic b` in a finite set,
then every nonempty subset `T` of `S` has a least element: intersect `T` with `Set.Iic t` for
some `t ∈ T`, which is finite and nonempty, and take its minimum. -/
theorem exists_isLeast_of_finite_inter_Iic (hfin : ∀ b : α, (S ∩ Set.Iic b).Finite)
    (hTS : T ⊆ S) (hT : T.Nonempty) : ∃ m : α, IsLeast T m := by
  obtain ⟨t, htT⟩ := hT
  have hsub : T ∩ Set.Iic t ⊆ S ∩ Set.Iic t := fun x hx => ⟨hTS hx.1, hx.2⟩
  obtain ⟨m, hm, hmin⟩ :=
    Set.exists_min_image (T ∩ Set.Iic t) id ((hfin t).subset hsub) ⟨t, htT, le_rfl⟩
  refine ⟨m, hm.1, ?_⟩
  intro x hxT
  rcases le_or_gt x t with hxt | hxt
  · exact hmin x ⟨hxT, hxt⟩
  · exact le_trans hm.2 hxt.le

/-- **An unbounded, locally finite subset of a linear order is order-isomorphic to `ℕ`.**  The
two set hypotheses become four instances on `↥S`: a least element gives `OrderBot`,
unboundedness gives `NoMaxOrder`, finiteness of `S ∩ Set.Iic b` gives `LocallyFiniteOrder`
through `LocallyFiniteOrder.ofFiniteIcc`, and that in turn gives the `SuccOrder`, `PredOrder`
and `IsSuccArchimedean` that `orderIsoNatOfLinearSuccPredArch` consumes. -/
theorem nonempty_orderIso_nat_of_unbounded_of_finite_inter_Iic [Nonempty α]
    (hub : ∀ b : α, ∃ x ∈ S, b < x) (hfin : ∀ b : α, (S ∩ Set.Iic b).Finite) :
    Nonempty (↥S ≃o ℕ) := by
  classical
  obtain ⟨x₀, hx₀, -⟩ := hub (Classical.arbitrary α)
  obtain ⟨m, hmS, hmlb⟩ := exists_isLeast_of_finite_inter_Iic hfin (subset_refl S) ⟨x₀, hx₀⟩
  let : OrderBot ↥S :=
    { bot := ⟨m, hmS⟩
      bot_le := fun a => hmlb a.2 }
  have : NoMaxOrder ↥S :=
    ⟨fun a => by
      obtain ⟨y, hyS, hy⟩ := hub (a : α)
      exact ⟨⟨y, hyS⟩, hy⟩⟩
  let : LocallyFiniteOrder ↥S :=
    LocallyFiniteOrder.ofFiniteIcc fun a b => by
      have himg : (Subtype.val '' Set.Icc a b : Set α) ⊆ S ∩ Set.Iic (b : α) := by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨z.2, hz.2⟩
      exact Set.Finite.of_finite_image ((hfin (b : α)).subset himg)
        Subtype.val_injective.injOn
  let : SuccOrder ↥S := LinearLocallyFiniteOrder.succOrder _
  let : PredOrder ↥S := LinearLocallyFiniteOrder.predOrder _
  exact ⟨orderIsoNatOfLinearSuccPredArch⟩

/-- **An unbounded, locally finite subset of a linear order is a strictly increasing sequence.**
This is the concrete form of `nonempty_orderIso_nat_of_unbounded_of_finite_inter_Iic`: the
inverse of the order isomorphism, read in `α`, is strictly monotone and its range is exactly
`S`, so `S = {f 0 < f 1 < f 2 < …}` with nothing omitted. -/
theorem exists_strictMono_range_eq_of_unbounded_of_finite_inter_Iic [Nonempty α]
    (hub : ∀ b : α, ∃ x ∈ S, b < x) (hfin : ∀ b : α, (S ∩ Set.Iic b).Finite) :
    ∃ f : ℕ → α, StrictMono f ∧ Set.range f = S := by
  obtain ⟨e⟩ := nonempty_orderIso_nat_of_unbounded_of_finite_inter_Iic hub hfin
  refine ⟨fun n => (e.symm n : α), fun i j hij => e.symm.strictMono hij, ?_⟩
  have hcomp : (fun n : ℕ => ((e.symm n : ↥S) : α)) = Subtype.val ∘ (e.symm : ℕ → ↥S) := rfl
  rw [hcomp, Set.range_comp, e.symm.surjective.range_eq, Set.image_univ, Subtype.range_coe]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex
public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing

/-!
# Extending maps along a regular pairing

Let `A` be a subcomplex of a simplicial set `X` with a regular pairing in the sense of Moss,
given by `h : A.PairingCore`. Mathlib's `SSet.Subcomplex.Pairing.RankFunction.relativeCellComplex`
exhibits `A.ι` as a relative cell complex: `X` is obtained from `A` by attaching, for each index
`s`, the simplex `h.simplex s` along the horn `Λ[h.dim s + 1, h.index s]`, in the order given by
a rank function. Consequently a map `A ⟶ C` extends to `X` as soon as every horn arising in this
process can be filled in `C`.

When every horn of the kinds attached can be filled in `C`, this extension property also follows
from `A.ι` being an anodyne extension of the corresponding kind. The point of the version here is
that the horn filling is only required for the horns that actually occur, and these may depend on
the map being extended: for instance, in a quasicategory, a horn `Λ[n + 2, 0]` can be
filled when its initial edge is an equivalence (Joyal's theorem), and whether this is the case
is decided by the given map `A ⟶ C` when that edge lies in `A`.

The same holds relative to a map `p : C ⟶ S`: a map `A ⟶ C` over `b : X ⟶ S` lifts to `X` over
`b` as soon as every horn arising in the process lifts along `p`. Over a point this is the
extension property. Relative to an inner fibration, for instance, a horn `Λ[n + 2, 0]` lifts when
its initial edge is coCartesian.

## Main results

* `SSet.Subcomplex.PairingCore.exists_lift_of_hornFilling`: a map `A ⟶ C` over `b : X ⟶ S` lifts
  along `p : C ⟶ S` to a map `X ⟶ C` over `b` when, for every index `s`, every such lift `g` of
  it to a subcomplex `B` of `X` restricts along the horn of `h.simplex s` to a horn of `C` which
  lifts along `p` over `b`.
* `SSet.Subcomplex.PairingCore.exists_ext_of_hornFilling`: a map `A ⟶ C` extends to `X` when,
  for every index `s`, every extension `g` of it to a subcomplex `B` of `X` restricts along the
  horn of `h.simplex s` to a horn of `C` which can be filled.

## References

* S. Moss, *Another approach to the Kan-Quillen model structure*, J. Homotopy Relat. Struct. 15
  (2020).
-/

public section

universe u

open CategoryTheory Limits Simplicial

namespace SSet.Subcomplex.PairingCore

variable {X C : SSet.{u}} {A : X.Subcomplex} (h : A.PairingCore) [h.IsRegular]

variable {S : SSet.{u}} (p : C ⟶ S)

/-- The horn lifting problem of a cell, transported from the cell of the rank function of the
pairing of `h` to the index of `h` it comes from. -/
private lemma exists_lift_cell (a : (A : SSet) ⟶ C) (b : X ⟶ S)
    (H : ∀ (s : h.ι) (B : X.Subcomplex) (hB : A ≤ B) (g : (B : SSet) ⟶ C),
      homOfLE hB ≫ g = a → g ≫ p = B.ι ≫ b →
        ∀ σ₀ : (Λ[h.dim s + 1, h.index s] : SSet) ⟶ B,
          σ₀ ≫ B.ι = Λ[h.dim s + 1, h.index s].ι ≫ yonedaEquiv.symm (h.simplex s) →
            ∃ σ : Δ[h.dim s + 1] ⟶ C, Λ[h.dim s + 1, h.index s].ι ≫ σ = σ₀ ≫ g ∧
              σ ≫ p = yonedaEquiv.symm (h.simplex s) ≫ b)
    (f : h.pairing.RankFunction ℕ) {j : ℕ} (c : f.Cell j) (g : (f.filtration j : SSet) ⟶ C)
    (hg : homOfLE (f.le_filtration j) ≫ g = a) (hgp : g ≫ p = (f.filtration j).ι ≫ b) :
    ∃ σ : Δ[c.dim + 1] ⟶ C, c.horn.ι ≫ σ = c.mapHorn ≫ g ∧ σ ≫ p = c.map ≫ b := by
  obtain ⟨x, hx⟩ := c
  obtain ⟨s, rfl⟩ := h.equivII.surjective x
  -- The cell attached at `h.equivII s` is the simplex `h.simplex s` along the horn at
  -- `h.index s`.
  let c : f.Cell j := ⟨h.equivII s, hx⟩
  have hmap : c.map = yonedaEquiv.symm (h.simplex s) := by
    have (y : A.N) (hy : y = h.type₁ s) (hd : y.dim = h.dim s + 1) :
        yonedaEquiv.symm (y.cast hd).simplex = yonedaEquiv.symm (h.simplex s) := by
      subst hy
      rfl
    exact this _ (congrArg Subtype.val (h.pairing_p_equivII s)) _
  have key : ∀ (i : Fin (h.dim s + 2)) (_ : i = h.index s)
      (σ₀ : (Λ[h.dim s + 1, i] : SSet) ⟶ f.filtration j),
      σ₀ ≫ (f.filtration j).ι =
        Λ[h.dim s + 1, i].ι ≫ yonedaEquiv.symm (h.simplex s) →
      ∃ σ : Δ[h.dim s + 1] ⟶ C, Λ[h.dim s + 1, i].ι ≫ σ = σ₀ ≫ g ∧
        σ ≫ p = yonedaEquiv.symm (h.simplex s) ≫ b := by
    rintro i rfl σ₀ hσ₀
    exact H s _ _ g hg hgp σ₀ hσ₀
  rw [hmap]
  exact key _ (h.index_pairing_equivII s) _
    ((Pairing.RankFunction.Cell.mapHorn_ι f c).trans (by rw [hmap]; rfl))

/-- The lift along the filtration of `X` given by a rank function `f` of the pairing of `h`,
built stage by stage. -/
private lemma exists_lift_of_rankFunction (f : h.pairing.RankFunction ℕ) (a : (A : SSet) ⟶ C)
    (b : X ⟶ S) (hab : a ≫ p = A.ι ≫ b)
    (H : ∀ (s : h.ι) (B : X.Subcomplex) (hB : A ≤ B) (g : (B : SSet) ⟶ C),
      homOfLE hB ≫ g = a → g ≫ p = B.ι ≫ b →
        ∀ σ₀ : (Λ[h.dim s + 1, h.index s] : SSet) ⟶ B,
          σ₀ ≫ B.ι = Λ[h.dim s + 1, h.index s].ι ≫ yonedaEquiv.symm (h.simplex s) →
            ∃ σ : Δ[h.dim s + 1] ⟶ C, Λ[h.dim s + 1, h.index s].ι ≫ σ = σ₀ ≫ g ∧
              σ ≫ p = yonedaEquiv.symm (h.simplex s) ≫ b) :
    ∃ l : X ⟶ C, A.ι ≫ l = a ∧ l ≫ p = b := by
  have hmono {i j : ℕ} (hij : i ≤ j) : f.filtration i ≤ f.filtration j := f.filtration_monotone hij
  -- The lifts of `a` to the stages of the filtration of `X` defined by `f`.
  let E : ℕ → Type u := fun j ↦
    {g : (f.filtration j : SSet) ⟶ C //
      homOfLE (f.le_filtration j) ≫ g = a ∧ g ≫ p = (f.filtration j).ι ≫ b}
  -- A lift to a stage extends to the next one, by filling the horns of the cells attached at
  -- that stage and using the pushout square `f.isPushout`.
  have step (j : ℕ) (g : E j) :
      ∃ g' : E (j + 1), homOfLE (hmono j.le_succ) ≫ g'.val = g.val := by
    choose σ hσ hσp using fun c : f.Cell j ↦
      exists_lift_cell h p a b H f c g.val g.property.1 g.property.2
    let g' : (f.filtration (Order.succ j) : SSet) ⟶ C :=
      (f.isPushout j).desc g.val (Sigma.desc σ) (by
        refine Sigma.hom_ext _ _ fun c ↦ ?_
        simp [hσ])
    have hg' : homOfLE (f.filtration_monotone (Order.le_succ j)) ≫ g' = g.val :=
      (f.isPushout j).inl_desc _ _ _
    have hg'p : g' ≫ p = (f.filtration (Order.succ j)).ι ≫ b := by
      refine (f.isPushout j).hom_ext ?_ (Sigma.hom_ext _ _ fun c ↦ ?_)
      · rw [reassoc_of% hg', g.property.2, Subcomplex.homOfLE_ι_assoc]
      · rw [(f.isPushout j).inr_desc_assoc, Sigma.ι_comp_desc_assoc, hσp,
          Pairing.RankFunction.Cell.ι_b_assoc, Pairing.RankFunction.Cell.mapToSucc_ι_assoc]
    have hg'a : homOfLE (f.le_filtration (Order.succ j)) ≫ g' = a := by
      rw [← g.property.1, ← hg', Subcomplex.homOfLE_comp_assoc]
    exact ⟨⟨g', hg'a, hg'p⟩, hg'⟩
  choose next hnext using step
  let seq : (j : ℕ) → E j := fun j ↦ Nat.rec
    ⟨homOfLE f.filtration_bot.le ≫ a, by
      rw [Subcomplex.homOfLE_comp_assoc, Subcomplex.homOfLE_refl, Category.id_comp], by
      rw [Category.assoc, hab, Subcomplex.homOfLE_ι_assoc]⟩
    (fun j g ↦ next j g) j
  have hseq {i j : ℕ} (hij : i ≤ j) : homOfLE (hmono hij) ≫ (seq j).val = (seq i).val := by
    induction j, hij using Nat.le_induction with
    | base => rw [Subcomplex.homOfLE_refl, Category.id_comp]
    | succ j hij ih =>
      rw [← ih, ← hnext j (seq j), Subcomplex.homOfLE_comp_assoc]
  -- The lifts are compatible, so they glue to `X`, the union of the filtration.
  let cocone : Cocone (f.filtration_monotone.functor ⋙ Subcomplex.toSSetFunctor) :=
    { pt := C
      ι := { app j := (seq j).val
             naturality i j hij := (hseq (leOfHom hij)).trans (Category.comp_id _).symm } }
  have hfac (j : ℕ) : (f.filtration j).ι ≫ f.relativeCellComplex.isColimit.desc cocone =
      (seq j).val :=
    f.relativeCellComplex.isColimit.fac cocone j
  refine ⟨f.relativeCellComplex.isColimit.desc cocone, ?_, ?_⟩
  · calc A.ι ≫ f.relativeCellComplex.isColimit.desc cocone
        = homOfLE (f.le_filtration 0) ≫ (f.filtration 0).ι ≫
            f.relativeCellComplex.isColimit.desc cocone := rfl
      _ = a := by rw [hfac]; exact (seq 0).property.1
  · refine f.relativeCellComplex.isColimit.hom_ext fun j ↦ ?_
    -- The legs of the colimit cocone of the filtration are the inclusions `(f.filtration j).ι`.
    exact ((reassoc_of% (hfac j)) p).trans (seq j).property.2

/-- **Lifting along a regular pairing.** Let `h` be a regular pairing of the subcomplex `A` of
`X`, and let `p : C ⟶ S`. A map `a : A ⟶ C` over `b : X ⟶ S` lifts to a map `X ⟶ C` over `b`
provided that, for every index `s` of `h`, every horn `Λ[h.dim s + 1, h.index s] ⟶ C` obtained by
restricting a lift `g : B ⟶ C` of `a` over `b`, defined on a subcomplex `B` of `X` containing the
horn of `h.simplex s`, lifts over `b` along the simplex `h.simplex s`. -/
theorem exists_lift_of_hornFilling (a : (A : SSet) ⟶ C) (b : X ⟶ S) (hab : a ≫ p = A.ι ≫ b)
    (H : ∀ (s : h.ι) (B : X.Subcomplex) (hB : A ≤ B) (g : (B : SSet) ⟶ C),
      homOfLE hB ≫ g = a → g ≫ p = B.ι ≫ b →
        ∀ σ₀ : (Λ[h.dim s + 1, h.index s] : SSet) ⟶ B,
          σ₀ ≫ B.ι = Λ[h.dim s + 1, h.index s].ι ≫ yonedaEquiv.symm (h.simplex s) →
            ∃ σ : Δ[h.dim s + 1] ⟶ C, Λ[h.dim s + 1, h.index s].ι ≫ σ = σ₀ ≫ g ∧
              σ ≫ p = yonedaEquiv.symm (h.simplex s) ≫ b) :
    ∃ l : X ⟶ C, A.ι ≫ l = a ∧ l ≫ p = b :=
  exists_lift_of_rankFunction h p h.pairing.rankFunction a b hab H

/-- **Extension along a regular pairing.** Let `h` be a regular pairing of the subcomplex `A` of
`X`. A map `a : A ⟶ C` extends to `X` provided that, for every index `s` of `h`, every horn
`Λ[h.dim s + 1, h.index s] ⟶ C` obtained by restricting an extension `g : B ⟶ C` of `a`, defined on
a subcomplex `B` of `X` containing the horn of `h.simplex s`, can be filled. This is the case of
`SSet.Subcomplex.PairingCore.exists_lift_of_hornFilling` over a point. -/
theorem exists_ext_of_hornFilling (a : (A : SSet) ⟶ C)
    (H : ∀ (s : h.ι) (B : X.Subcomplex) (hB : A ≤ B) (g : (B : SSet) ⟶ C),
      homOfLE hB ≫ g = a → ∀ σ₀ : (Λ[h.dim s + 1, h.index s] : SSet) ⟶ B,
        σ₀ ≫ B.ι = Λ[h.dim s + 1, h.index s].ι ≫ yonedaEquiv.symm (h.simplex s) →
          ∃ σ : Δ[h.dim s + 1] ⟶ C, Λ[h.dim s + 1, h.index s].ι ≫ σ = σ₀ ≫ g) :
    ∃ b : X ⟶ C, A.ι ≫ b = a := by
  let T := stdSimplex.isTerminalObj₀.{u}
  obtain ⟨l, hl, -⟩ := exists_lift_of_hornFilling h (T.from C) a (T.from X) (T.hom_ext _ _)
    fun s B hB g hg _ σ₀ hσ₀ ↦ (H s B hB g hg σ₀ hσ₀).imp fun _ hσ ↦ ⟨hσ, T.hom_ext _ _⟩
  exact ⟨l, hl⟩

end SSet.Subcomplex.PairingCore

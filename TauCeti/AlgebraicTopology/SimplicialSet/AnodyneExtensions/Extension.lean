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

## Main results

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

/-- The horn filling problem of a cell, transported from the cell of the rank function of the
pairing of `h` to the index of `h` it comes from. -/
private lemma exists_fill_cell (a : (A : SSet) ⟶ C)
    (H : ∀ (s : h.ι) (B : X.Subcomplex) (hB : A ≤ B) (g : (B : SSet) ⟶ C),
      homOfLE hB ≫ g = a → ∀ σ₀ : (Λ[h.dim s + 1, h.index s] : SSet) ⟶ B,
        σ₀ ≫ B.ι = Λ[h.dim s + 1, h.index s].ι ≫ yonedaEquiv.symm (h.simplex s) →
          ∃ σ : Δ[h.dim s + 1] ⟶ C, Λ[h.dim s + 1, h.index s].ι ≫ σ = σ₀ ≫ g)
    (f : h.pairing.RankFunction ℕ) {j : ℕ} (c : f.Cell j) (g : (f.filtration j : SSet) ⟶ C)
    (hg : homOfLE (f.le_filtration j) ≫ g = a) :
    ∃ σ : Δ[c.dim + 1] ⟶ C, c.horn.ι ≫ σ = c.mapHorn ≫ g := by
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
      ∃ σ : Δ[h.dim s + 1] ⟶ C, Λ[h.dim s + 1, i].ι ≫ σ = σ₀ ≫ g := by
    rintro i rfl σ₀ hσ₀
    exact H s _ _ g hg σ₀ hσ₀
  exact key _ (h.index_pairing_equivII s) _
    ((Pairing.RankFunction.Cell.mapHorn_ι f c).trans (by rw [hmap]; rfl))

/-- The extension along the filtration of `X` given by a rank function `f` of the pairing of `h`,
built stage by stage. -/
private lemma exists_ext_of_rankFunction (f : h.pairing.RankFunction ℕ) (a : (A : SSet) ⟶ C)
    (H : ∀ (s : h.ι) (B : X.Subcomplex) (hB : A ≤ B) (g : (B : SSet) ⟶ C),
      homOfLE hB ≫ g = a → ∀ σ₀ : (Λ[h.dim s + 1, h.index s] : SSet) ⟶ B,
        σ₀ ≫ B.ι = Λ[h.dim s + 1, h.index s].ι ≫ yonedaEquiv.symm (h.simplex s) →
          ∃ σ : Δ[h.dim s + 1] ⟶ C, Λ[h.dim s + 1, h.index s].ι ≫ σ = σ₀ ≫ g) :
    ∃ b : X ⟶ C, A.ι ≫ b = a := by
  have hmono {i j : ℕ} (hij : i ≤ j) : f.filtration i ≤ f.filtration j := f.filtration_monotone hij
  -- The extensions of `a` to the stages of the filtration of `X` defined by `f`.
  let E : ℕ → Type u := fun j ↦
    {g : (f.filtration j : SSet) ⟶ C // homOfLE (f.le_filtration j) ≫ g = a}
  -- An extension to a stage extends to the next one, by filling the horns of the cells attached
  -- at that stage and using the pushout square `f.isPushout`.
  have step (j : ℕ) (g : E j) :
      ∃ g' : E (j + 1), homOfLE (hmono j.le_succ) ≫ g'.val = g.val := by
    choose σ hσ using fun c : f.Cell j ↦ exists_fill_cell h a H f c g.val g.property
    let g' : (f.filtration (j + 1) : SSet) ⟶ C := (f.isPushout j).desc g.val (Sigma.desc σ) (by
      refine Sigma.hom_ext _ _ fun c ↦ ?_
      simp [hσ])
    have hg' : homOfLE (hmono j.le_succ) ≫ g' = g.val :=
      (f.isPushout j).inl_desc _ _ _
    refine ⟨⟨g', ?_⟩, hg'⟩
    rw [← g.property, ← hg', Subcomplex.homOfLE_comp_assoc]
  choose next hnext using step
  let seq : (j : ℕ) → E j := fun j ↦ Nat.rec
    ⟨homOfLE f.filtration_bot.le ≫ a, by
      rw [Subcomplex.homOfLE_comp_assoc, Subcomplex.homOfLE_refl, Category.id_comp]⟩
    (fun j g ↦ next j g) j
  have hseq {i j : ℕ} (hij : i ≤ j) : homOfLE (hmono hij) ≫ (seq j).val = (seq i).val := by
    induction j, hij using Nat.le_induction with
    | base => rw [Subcomplex.homOfLE_refl, Category.id_comp]
    | succ j hij ih =>
      rw [← ih, ← hnext j (seq j), Subcomplex.homOfLE_comp_assoc]
  -- The extensions are compatible, so they glue to `X`, the union of the filtration.
  let cocone : Cocone (f.filtration_monotone.functor ⋙ Subcomplex.toSSetFunctor) :=
    { pt := C
      ι := { app j := (seq j).val
             naturality i j hij := (hseq (leOfHom hij)).trans (Category.comp_id _).symm } }
  refine ⟨f.relativeCellComplex.isColimit.desc cocone, ?_⟩
  have h₀ : (f.filtration 0).ι ≫ f.relativeCellComplex.isColimit.desc cocone = (seq 0).val :=
    f.relativeCellComplex.isColimit.fac cocone 0
  calc A.ι ≫ f.relativeCellComplex.isColimit.desc cocone
      = homOfLE (f.le_filtration 0) ≫ (f.filtration 0).ι ≫
          f.relativeCellComplex.isColimit.desc cocone := rfl
    _ = a := by rw [h₀]; exact (seq 0).property

/-- **Extension along a regular pairing.** Let `h` be a regular pairing of the subcomplex `A` of
`X`. A map `a : A ⟶ C` extends to `X` provided that, for every index `s` of `h`, every horn
`Λ[h.dim s + 1, h.index s] ⟶ C` obtained by restricting an extension `g : B ⟶ C` of `a`, defined on
a subcomplex `B` of `X` containing the horn of `h.simplex s`, can be filled. -/
theorem exists_ext_of_hornFilling (a : (A : SSet) ⟶ C)
    (H : ∀ (s : h.ι) (B : X.Subcomplex) (hB : A ≤ B) (g : (B : SSet) ⟶ C),
      homOfLE hB ≫ g = a → ∀ σ₀ : (Λ[h.dim s + 1, h.index s] : SSet) ⟶ B,
        σ₀ ≫ B.ι = Λ[h.dim s + 1, h.index s].ι ≫ yonedaEquiv.symm (h.simplex s) →
          ∃ σ : Δ[h.dim s + 1] ⟶ C, Λ[h.dim s + 1, h.index s].ι ≫ σ = σ₀ ≫ g) :
    ∃ b : X ⟶ C, A.ι ≫ b = a :=
  exists_ext_of_rankFunction h h.pairing.rankFunction a H

end SSet.Subcomplex.PairingCore

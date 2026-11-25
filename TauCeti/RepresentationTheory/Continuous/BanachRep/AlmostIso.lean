/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.RepresentationTheory.Continuous.BanachRep.Basic
import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# Almost isomorphisms of Banach representations

Two Banach representations `X` and `Y` of a topological monoid `G` over a complete nontrivially
normed field `𝕜` are *almost isomorphic* when they become isomorphic after dividing each by a
finite-dimensional invariant subspace: there are such subspaces `A ⊆ X` and `B ⊆ Y` and an
isomorphism `X ⧸ A ≅ Y ⧸ B` of Banach representations. Finite-dimensional subspaces of a Banach
space over a complete field are closed, so both quotients are again Banach representations.

This is Fontaine's notion, on which the category of almost `C`-representations is built: a
Banach representation of the absolute Galois group of a `p`-adic field is an almost
`C`-representation when it is almost isomorphic to a finite power `C^d` of the completed
algebraic closure. The *height* of an almost isomorphism is the signed integer
`dim A - dim B`. For almost `C`-representations of the Galois group of a finite extension of
`ℚ_p` it is independent of the choice of almost isomorphism, by Fontaine's structure theorem; in
general it is an invariant of the almost isomorphism only.

Almost isomorphism is an equivalence relation. Reflexivity and symmetry are immediate.
Transitivity uses a common refinement: if `X ⧸ A ≅ Y ⧸ B` and `Y ⧸ B' ≅ Z ⧸ C`, both
isomorphisms are refined to quotients by the finite-dimensional subspace `B ⊔ B'` of `Y`, and the
heights add up.

## Main definitions

* `TauCeti.BanachRep.AlmostIso X Y`: an almost isomorphism, given by finite-dimensional invariant
  subspaces `left ⊆ X`, `right ⊆ Y` and an isomorphism `iso` of the quotients.
* `TauCeti.BanachRep.AlmostIso.height`: the integer `dim left - dim right`.
* `TauCeti.BanachRep.AlmostIso.refl`, `TauCeti.BanachRep.AlmostIso.symm` and
  `TauCeti.BanachRep.AlmostIso.trans`: almost isomorphism is an equivalence relation.
* `TauCeti.BanachRep.AlmostIso.ofSurjective`: a surjective morphism `X ⟶ Y ⧸ B` with
  finite-dimensional kernel gives an almost isomorphism.
* `TauCeti.BanachRep.AlmostIso.ofIso`, `TauCeti.BanachRep.AlmostIso.toQuotient` and
  `TauCeti.BanachRep.AlmostIso.ofFiniteDimensional`: an isomorphism, the projection onto a
  quotient by a finite-dimensional invariant subspace, and any two finite-dimensional
  representations give almost isomorphisms.

## Main results

* `TauCeti.BanachRep.AlmostIso.height_symm` and `TauCeti.BanachRep.AlmostIso.height_trans`: the
  height changes sign under inversion and is additive under composition.
* `TauCeti.BanachRep.AlmostIso.equivalence`: being almost isomorphic is an equivalence relation.

## References

* J.-M. Fontaine, *Presque `C_p`-représentations*, Documenta Mathematica, Extra Volume Kato
  (2003), 285–385, §1.4.
* P. Colmez and W. Nizioł, *On the cohomology of `p`-adic analytic spaces, II: The
  `C_st`-conjecture* (2025), §2.2.1 and Remark 2.3.
-/

public section

universe w u v

open CategoryTheory CategoryTheory.Limits Module

namespace TauCeti

namespace BanachRep

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {G : Type v} [Monoid G]
  [TopologicalSpace G] {X Y Z : BanachRep.{w} 𝕜 G}

/-- **An almost isomorphism** between Banach representations `X` and `Y`: finite-dimensional
invariant subspaces `left ⊆ X` and `right ⊆ Y` together with an isomorphism
`X ⧸ left ≅ Y ⧸ right` of Banach representations. -/
structure AlmostIso (X Y : BanachRep.{w} 𝕜 G) where
  /-- The finite-dimensional invariant subspace divided out of `X`. -/
  left : Submodule 𝕜 X
  /-- The finite-dimensional invariant subspace divided out of `Y`. -/
  right : Submodule 𝕜 Y
  [finiteDimensional_left : FiniteDimensional 𝕜 left]
  [finiteDimensional_right : FiniteDimensional 𝕜 right]
  /-- The subspace divided out of `X` is invariant. -/
  left_invariant : ∀ (g : G), ∀ x ∈ left, X.ρ g x ∈ left
  /-- The subspace divided out of `Y` is invariant. -/
  right_invariant : ∀ (g : G), ∀ y ∈ right, Y.ρ g y ∈ right
  /-- The isomorphism between the two quotients. -/
  iso : quotient X left left_invariant left.isClosed_of_finiteDimensional ≅
    quotient Y right right_invariant right.isClosed_of_finiteDimensional

namespace AlmostIso

attribute [instance] finiteDimensional_left finiteDimensional_right

/-- The height of an almost isomorphism: the dimension of the subspace divided out of the source
minus the dimension of the subspace divided out of the target. -/
noncomputable def height (e : AlmostIso X Y) : ℤ :=
  finrank 𝕜 e.left - finrank 𝕜 e.right

theorem height_def (e : AlmostIso X Y) : e.height = finrank 𝕜 e.left - finrank 𝕜 e.right :=
  (rfl)

/-- The morphism `X ⟶ Y ⧸ right` underlying an almost isomorphism: the projection onto
`X ⧸ left`, followed by the isomorphism of quotients. -/
noncomputable def proj (e : AlmostIso X Y) :
    X ⟶ quotient Y e.right e.right_invariant e.right.isClosed_of_finiteDimensional :=
  quotientπ X e.left e.left_invariant e.left.isClosed_of_finiteDimensional ≫ e.iso.hom

theorem proj_def (e : AlmostIso X Y) :
    e.proj = quotientπ X e.left e.left_invariant e.left.isClosed_of_finiteDimensional ≫ e.iso.hom :=
  (rfl)

theorem proj_surjective (e : AlmostIso X Y) : Function.Surjective e.proj.hom :=
  ((bijective_of_isIso e.iso.hom).2.comp (quotientπ_surjective _ _ _ _) :)

/-- The kernel of the morphism `X ⟶ Y ⧸ right` is the subspace divided out of `X`. -/
@[simp]
theorem ker_proj (e : AlmostIso X Y) : LinearMap.ker e.proj.hom.toLinearMap = e.left := by
  ext x
  simp only [LinearMap.mem_ker, proj, hom_comp, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply]
  rw [← (quotientπ_hom_apply_eq_zero_iff X e.left e.left_invariant
    e.left.isClosed_of_finiteDimensional x)]
  exact (bijective_of_isIso e.iso.hom).1.eq_iff' (map_zero _)

instance (e : AlmostIso X Y) : FiniteDimensional 𝕜 (LinearMap.ker e.proj.hom.toLinearMap) := by
  rw [ker_proj]
  infer_instance

/-! ### Constructions -/

/-- **The identity almost isomorphism**, dividing out the zero subspace on both sides. -/
@[expose] noncomputable def refl (X : BanachRep.{w} 𝕜 G) : AlmostIso X X where
  left := ⊥
  right := ⊥
  left_invariant := bot_invariant X
  right_invariant := bot_invariant X
  iso := Iso.refl _

@[simp]
theorem refl_left (X : BanachRep.{w} 𝕜 G) : (refl X).left = ⊥ :=
  (rfl)

@[simp]
theorem refl_right (X : BanachRep.{w} 𝕜 G) : (refl X).right = ⊥ :=
  (rfl)

@[simp]
theorem refl_iso (X : BanachRep.{w} 𝕜 G) : (refl X).iso = Iso.refl _ :=
  (rfl)

@[simp]
theorem height_refl (X : BanachRep.{w} 𝕜 G) : (refl X).height = 0 := by
  rw [height_def, refl_left, refl_right, sub_self]

/-- **The inverse almost isomorphism**, exchanging the two sides. -/
@[expose] noncomputable def symm (e : AlmostIso X Y) : AlmostIso Y X where
  left := e.right
  right := e.left
  left_invariant := e.right_invariant
  right_invariant := e.left_invariant
  iso := e.iso.symm

@[simp]
theorem symm_left (e : AlmostIso X Y) : e.symm.left = e.right :=
  (rfl)

@[simp]
theorem symm_right (e : AlmostIso X Y) : e.symm.right = e.left :=
  (rfl)

@[simp]
theorem symm_iso (e : AlmostIso X Y) : e.symm.iso = e.iso.symm :=
  (rfl)

/-- The morphism underlying the inverse almost isomorphism is the projection onto `Y ⧸ right`,
followed by the inverse of the isomorphism of quotients. -/
@[simp]
theorem symm_proj (e : AlmostIso X Y) :
    e.symm.proj =
      quotientπ Y e.right e.right_invariant e.right.isClosed_of_finiteDimensional ≫ e.iso.inv :=
  (rfl)

@[simp]
theorem height_symm (e : AlmostIso X Y) : e.symm.height = -e.height := by
  rw [height_def, height_def, symm_left, symm_right, neg_sub]

@[simp]
theorem symm_symm (e : AlmostIso X Y) : e.symm.symm = e :=
  (rfl)

/-- **A surjective morphism `X ⟶ Y ⧸ B` with finite-dimensional kernel is an almost
isomorphism**, dividing out its kernel on the left and `B` on the right. -/
@[expose] noncomputable def ofSurjective (B : Submodule 𝕜 Y) [FiniteDimensional 𝕜 B]
    (hB : ∀ (g : G), ∀ y ∈ B, Y.ρ g y ∈ B)
    (f : X ⟶ quotient Y B hB B.isClosed_of_finiteDimensional) (hf : Function.Surjective f.hom)
    [FiniteDimensional 𝕜 (LinearMap.ker f.hom.toLinearMap)] : AlmostIso X Y where
  left := LinearMap.ker f.hom.toLinearMap
  right := B
  left_invariant := ker_invariant f
  right_invariant := hB
  iso :=
    have := isIso_quotientDesc_ker f hf
    asIso (quotientDesc X _ (ker_invariant f) (Submodule.isClosed_of_finiteDimensional _) f
      fun _ hx => hx)

@[simp]
theorem ofSurjective_left (B : Submodule 𝕜 Y) [FiniteDimensional 𝕜 B]
    (hB : ∀ (g : G), ∀ y ∈ B, Y.ρ g y ∈ B)
    (f : X ⟶ quotient Y B hB B.isClosed_of_finiteDimensional) (hf : Function.Surjective f.hom)
    [FiniteDimensional 𝕜 (LinearMap.ker f.hom.toLinearMap)] :
    (ofSurjective B hB f hf).left = LinearMap.ker f.hom.toLinearMap :=
  (rfl)

@[simp]
theorem ofSurjective_right (B : Submodule 𝕜 Y) [FiniteDimensional 𝕜 B]
    (hB : ∀ (g : G), ∀ y ∈ B, Y.ρ g y ∈ B)
    (f : X ⟶ quotient Y B hB B.isClosed_of_finiteDimensional) (hf : Function.Surjective f.hom)
    [FiniteDimensional 𝕜 (LinearMap.ker f.hom.toLinearMap)] : (ofSurjective B hB f hf).right = B :=
  (rfl)

/-- The morphism underlying the almost isomorphism built from a surjective morphism `f` is `f`. -/
@[simp]
theorem ofSurjective_proj (B : Submodule 𝕜 Y) [FiniteDimensional 𝕜 B]
    (hB : ∀ (g : G), ∀ y ∈ B, Y.ρ g y ∈ B)
    (f : X ⟶ quotient Y B hB B.isClosed_of_finiteDimensional) (hf : Function.Surjective f.hom)
    [FiniteDimensional 𝕜 (LinearMap.ker f.hom.toLinearMap)] : (ofSurjective B hB f hf).proj = f :=
  quotientπ_comp_quotientDesc X _ _ _ f _

@[simp]
theorem height_ofSurjective (B : Submodule 𝕜 Y) [FiniteDimensional 𝕜 B]
    (hB : ∀ (g : G), ∀ y ∈ B, Y.ρ g y ∈ B)
    (f : X ⟶ quotient Y B hB B.isClosed_of_finiteDimensional) (hf : Function.Surjective f.hom)
    [FiniteDimensional 𝕜 (LinearMap.ker f.hom.toLinearMap)] :
    (ofSurjective B hB f hf).height =
      finrank 𝕜 (LinearMap.ker f.hom.toLinearMap) - finrank 𝕜 B :=
  (rfl)

/-- **An isomorphism is an almost isomorphism**, dividing out the zero subspace on both sides. -/
@[expose] noncomputable def ofIso (f : X ≅ Y) : AlmostIso X Y where
  left := ⊥
  right := ⊥
  left_invariant := bot_invariant X
  right_invariant := bot_invariant Y
  iso :=
    (asIso (quotientπ X ⊥ (bot_invariant X) (Submodule.isClosed_of_finiteDimensional _))).symm ≪≫
      f ≪≫ asIso (quotientπ Y ⊥ (bot_invariant Y) (Submodule.isClosed_of_finiteDimensional _))

@[simp]
theorem ofIso_left (f : X ≅ Y) : (ofIso f).left = ⊥ :=
  (rfl)

@[simp]
theorem ofIso_right (f : X ≅ Y) : (ofIso f).right = ⊥ :=
  (rfl)

/-- The morphism underlying the almost isomorphism built from an isomorphism `f` is `f` followed
by the projection onto the quotient by the zero subspace. -/
@[simp]
theorem ofIso_proj (f : X ≅ Y) :
    (ofIso f).proj =
      f.hom ≫ quotientπ Y ⊥ (bot_invariant Y) (Submodule.isClosed_of_finiteDimensional _) := by
  simp [proj, ofIso]

@[simp]
theorem height_ofIso (f : X ≅ Y) : (ofIso f).height = 0 := by
  rw [height_def, ofIso_left, ofIso_right, finrank_bot, finrank_bot, sub_self]

/-- **A representation is almost isomorphic to its quotient by a finite-dimensional invariant
subspace** `A`, dividing out `A` on the left and the zero subspace on the right. -/
@[expose] noncomputable def toQuotient (X : BanachRep.{w} 𝕜 G) (A : Submodule 𝕜 X)
    [FiniteDimensional 𝕜 A] (hA : ∀ (g : G), ∀ x ∈ A, X.ρ g x ∈ A) :
    AlmostIso X (quotient X A hA A.isClosed_of_finiteDimensional) where
  left := A
  right := ⊥
  left_invariant := hA
  right_invariant := bot_invariant _
  iso :=
    -- `quotient` is a reducible abbreviation, so instance search does not find
    -- `isIso_quotientπ_bot` for a quotient of a quotient; it is supplied by hand.
    have := isIso_quotientπ_bot (quotient X A hA A.isClosed_of_finiteDimensional)
      (bot_invariant _) (Submodule.isClosed_of_finiteDimensional _)
    asIso (quotientπ _ ⊥ _ _)

@[simp]
theorem toQuotient_left (X : BanachRep.{w} 𝕜 G) (A : Submodule 𝕜 X) [FiniteDimensional 𝕜 A]
    (hA : ∀ (g : G), ∀ x ∈ A, X.ρ g x ∈ A) : (toQuotient X A hA).left = A :=
  (rfl)

@[simp]
theorem toQuotient_right (X : BanachRep.{w} 𝕜 G) (A : Submodule 𝕜 X) [FiniteDimensional 𝕜 A]
    (hA : ∀ (g : G), ∀ x ∈ A, X.ρ g x ∈ A) : (toQuotient X A hA).right = ⊥ :=
  (rfl)

/-- The morphism underlying the almost isomorphism onto a quotient is the projection onto that
quotient, followed by the projection onto its quotient by the zero subspace. -/
@[simp]
theorem toQuotient_proj (X : BanachRep.{w} 𝕜 G) (A : Submodule 𝕜 X) [FiniteDimensional 𝕜 A]
    (hA : ∀ (g : G), ∀ x ∈ A, X.ρ g x ∈ A) :
    (toQuotient X A hA).proj = quotientπ X A hA A.isClosed_of_finiteDimensional ≫
      quotientπ _ ⊥ (bot_invariant _) (Submodule.isClosed_of_finiteDimensional _) :=
  (rfl)

@[simp]
theorem height_toQuotient (X : BanachRep.{w} 𝕜 G) (A : Submodule 𝕜 X) [FiniteDimensional 𝕜 A]
    (hA : ∀ (g : G), ∀ x ∈ A, X.ρ g x ∈ A) : (toQuotient X A hA).height = finrank 𝕜 A := by
  rw [height_def, toQuotient_left, toQuotient_right, finrank_bot, Nat.cast_zero, sub_zero]

/-- **Two finite-dimensional representations are almost isomorphic**, dividing out each of them
entirely. -/
noncomputable def ofFiniteDimensional (X Y : BanachRep.{w} 𝕜 G) [FiniteDimensional 𝕜 X]
    [FiniteDimensional 𝕜 Y] : AlmostIso X Y where
  left := ⊤
  right := ⊤
  left_invariant := top_invariant X
  right_invariant := top_invariant Y
  iso := (isZero_quotient_top X _ _).iso (isZero_quotient_top Y _ _)

@[simp]
theorem ofFiniteDimensional_left (X Y : BanachRep.{w} 𝕜 G) [FiniteDimensional 𝕜 X]
    [FiniteDimensional 𝕜 Y] : (ofFiniteDimensional X Y).left = ⊤ :=
  (rfl)

@[simp]
theorem ofFiniteDimensional_right (X Y : BanachRep.{w} 𝕜 G) [FiniteDimensional 𝕜 X]
    [FiniteDimensional 𝕜 Y] : (ofFiniteDimensional X Y).right = ⊤ :=
  (rfl)

@[simp]
theorem height_ofFiniteDimensional (X Y : BanachRep.{w} 𝕜 G) [FiniteDimensional 𝕜 X]
    [FiniteDimensional 𝕜 Y] :
    (ofFiniteDimensional X Y).height = finrank 𝕜 X - finrank 𝕜 Y := by
  rw [height_def, ofFiniteDimensional_left, ofFiniteDimensional_right, finrank_top, finrank_top]

/-! ### Refinement and composition -/

section Refine

variable (e : AlmostIso X Y) (B : Submodule 𝕜 Y) [FiniteDimensional 𝕜 B]
  (hB : ∀ (g : G), ∀ y ∈ B, Y.ρ g y ∈ B) (h : e.right ≤ B)

private theorem ker_proj_comp_quotientFactor :
    LinearMap.ker
        (e.proj ≫ quotientFactor Y _ _ hB B.isClosed_of_finiteDimensional h).hom.toLinearMap =
      (B.map e.right.mkQ).comap e.proj.hom.toLinearMap := by
  rw [hom_comp, ContinuousLinearMap.toLinearMap_comp, LinearMap.ker_comp, ker_quotientFactor]

/-- **Refining an almost isomorphism**: an almost isomorphism `X ⧸ A ≅ Y ⧸ right` induces one
dividing out any larger finite-dimensional invariant subspace `B ⊇ right` of `Y`, with the
preimage of `B ⧸ right` divided out of `X`. -/
@[expose] noncomputable def refineRight : AlmostIso X Y :=
  have : FiniteDimensional 𝕜 (LinearMap.ker
      (e.proj ≫ quotientFactor Y _ _ hB B.isClosed_of_finiteDimensional h).hom.toLinearMap) := by
    rw [ker_proj_comp_quotientFactor]
    infer_instance
  ofSurjective B hB (e.proj ≫ quotientFactor Y _ _ hB B.isClosed_of_finiteDimensional h) (by
    rw [hom_comp, ContinuousLinearMap.coe_comp]
    exact (quotientFactor_surjective Y _ _ hB _ h).comp e.proj_surjective)

/-- Refining an almost isomorphism divides out of `X` the preimage of `B ⧸ right`. -/
@[simp]
theorem refineRight_left :
    (e.refineRight B hB h).left = (B.map e.right.mkQ).comap e.proj.hom.toLinearMap :=
  ker_proj_comp_quotientFactor e B hB h

@[simp]
theorem refineRight_right : (e.refineRight B hB h).right = B :=
  (rfl)

/-- The morphism underlying a refined almost isomorphism is the original one followed by the
projection `Y ⧸ right ⟶ Y ⧸ B`. -/
@[simp]
theorem refineRight_proj :
    (e.refineRight B hB h).proj =
      e.proj ≫ quotientFactor Y _ _ hB B.isClosed_of_finiteDimensional h :=
  quotientπ_comp_quotientDesc X _ _ _ _ _

/-- Refining an almost isomorphism does not change its height: the subspaces divided out on
both sides grow by the dimension of `B ⧸ right`. -/
@[simp]
theorem height_refineRight : (e.refineRight B hB h).height = e.height := by
  have hX := LinearMap.finrank_comap_of_surjective e.proj_surjective (B.map e.right.mkQ)
  have : FiniteDimensional 𝕜 (LinearMap.ker e.right.mkQ) := by
    rw [Submodule.ker_mkQ]
    infer_instance
  have hY := LinearMap.finrank_comap_of_surjective e.right.mkQ_surjective (B.map e.right.mkQ)
  rw [Submodule.comap_map_mkQ, sup_eq_right.mpr h, Submodule.ker_mkQ] at hY
  rw [ker_proj] at hX
  rw [refineRight, height_ofSurjective, ker_proj_comp_quotientFactor, hX, hY, height_def]
  push_cast
  ring

end Refine

/-- **Composition of almost isomorphisms**: if `X ⧸ A ≅ Y ⧸ B` and `Y ⧸ B' ≅ Z ⧸ C`, both are
refined to almost isomorphisms dividing out `B ⊔ B'` from `Y` (`refineRight`), and composed
there. -/
@[expose] noncomputable def trans (e : AlmostIso X Y) (f : AlmostIso Y Z) : AlmostIso X Z where
  left := (e.refineRight _ (sup_invariant e.right_invariant f.left_invariant) le_sup_left).left
  right := (f.symm.refineRight _ (sup_invariant e.right_invariant f.left_invariant)
    le_sup_right).left
  left_invariant := (e.refineRight _ _ le_sup_left).left_invariant
  right_invariant := (f.symm.refineRight _ _ le_sup_right).left_invariant
  iso := (e.refineRight _ (sup_invariant e.right_invariant f.left_invariant) le_sup_left).iso ≪≫
    (f.symm.refineRight _ (sup_invariant e.right_invariant f.left_invariant) le_sup_right).iso.symm

/-- A composite almost isomorphism divides out of `X` the preimage of `(B ⊔ B') ⧸ B`. -/
@[simp]
theorem trans_left (e : AlmostIso X Y) (f : AlmostIso Y Z) :
    (e.trans f).left = ((e.right ⊔ f.left).map e.right.mkQ).comap e.proj.hom.toLinearMap :=
  refineRight_left e _ (sup_invariant e.right_invariant f.left_invariant) le_sup_left

/-- A composite almost isomorphism divides out of `Z` the preimage of `(B ⊔ B') ⧸ B'`. -/
@[simp]
theorem trans_right (e : AlmostIso X Y) (f : AlmostIso Y Z) :
    (e.trans f).right = ((e.right ⊔ f.left).map f.left.mkQ).comap f.symm.proj.hom.toLinearMap :=
  refineRight_left f.symm _ (sup_invariant e.right_invariant f.left_invariant) le_sup_right

/-- A composite almost isomorphism is the composite of the two refinements of its factors
dividing out `B ⊔ B'` from `Y`. -/
theorem trans_iso (e : AlmostIso X Y) (f : AlmostIso Y Z) :
    (e.trans f).iso =
      (e.refineRight _ (sup_invariant e.right_invariant f.left_invariant) le_sup_left).iso ≪≫
        (f.symm.refineRight _ (sup_invariant e.right_invariant f.left_invariant)
          le_sup_right).iso.symm :=
  (rfl)

/-- **The height is additive under composition of almost isomorphisms.** -/
@[simp]
theorem height_trans (e : AlmostIso X Y) (f : AlmostIso Y Z) :
    (e.trans f).height = e.height + f.height := by
  have hD := sup_invariant e.right_invariant f.left_invariant
  have h' : f.symm.right ≤ e.right ⊔ f.left := by
    rw [symm_right]
    exact le_sup_right
  have he := height_refineRight e (e.right ⊔ f.left) hD le_sup_left
  have hf := height_refineRight f.symm (e.right ⊔ f.left) hD h'
  rw [height_symm] at hf
  rw [height_def (e.refineRight (e.right ⊔ f.left) hD le_sup_left), refineRight_left,
    refineRight_right] at he
  rw [height_def (f.symm.refineRight (e.right ⊔ f.left) hD h'), refineRight_left,
    refineRight_right] at hf
  rw [height_def, trans_left, trans_right]
  -- `hf` quotients by `f.symm.right` where `trans_right` has `f.left`. The two agree by
  -- `symm_right`, which `rw` cannot apply under the dependent `mkQ`, so `ring1!` matches them.
  linear_combination (norm := ring1!) he - hf

/-- **Being almost isomorphic is an equivalence relation.** -/
theorem equivalence :
    Equivalence fun X Y : BanachRep.{w} 𝕜 G => Nonempty (AlmostIso X Y) where
  refl X := ⟨refl X⟩
  symm := fun ⟨e⟩ => ⟨e.symm⟩
  trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩

end AlmostIso

end BanachRep

end TauCeti

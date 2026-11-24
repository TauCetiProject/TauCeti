/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Points
public import TauCeti.AlgebraicGeometry.Scheme.AffinePoints
public import TauCeti.RingTheory.Grassmannian.Plucker

/-!
# The Plücker morphism of the Grassmannian scheme

Let `M` be a module over a commutative ring `R` and `k` a natural number. This file constructs the
**Plücker morphism** `G(k, M) ⟶ G(1, ⋀ᵏ M)` over `Spec R` between the Grassmannian schemes
`Module.Grassmannian.scheme R M k` and `Module.Grassmannian.scheme R (⋀[R]^k M) 1`, the latter
the projective bundle `P(⋀ᵏ M)` of rank-one quotients. On points over an `R`-algebra `A` it sends
the point classifying `N ⊆ A ⊗[R] M` to the point classifying the kernel of
`⋀ᵏ_A (A ⊗[R] M) → ⋀ᵏ_A ((A ⊗[R] M) ⧸ N)`, read in `A ⊗[R] ⋀ᵏ M`
(`Module.Grassmannian.pluckerBaseChange`): the universal exterior-power quotient
`⋀ᵏ E_T → det Q` of the roadmaps.

The point map is natural in `A` (`Module.Grassmannian.pluckerBaseChange_map`), so it is composition
with a morphism of schemes (`AlgebraicGeometry.Scheme.homOfAffinePoints`), as for the base change
morphism `Module.Grassmannian.baseChangeHom`.

## Main definitions

* `Module.Grassmannian.pluckerHom R M k`: the Plücker morphism `G(k, M) ⟶ G(1, ⋀ᵏ M)`.

## Main results

* `Module.Grassmannian.toSchemeHom_comp_pluckerHom`: the characterisation of `pluckerHom` on
  points.
* `Module.Grassmannian.pluckerHom_toSpec`: `pluckerHom` lies over `Spec R`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (k : ℕ)

/-- The morphism `Spec A ⟶ G(1, ⋀ᵏ M)` classifying the Plücker point of the point of
`G(k, A ⊗[R] M; A)` classified by `a`. The algebra structure on `A` is an explicit argument, so
that `pluckerAux_congr` can compare different choices. -/
private noncomputable def pluckerAux (A : Type u) [CommRing A] (_ : Algebra R A)
    (a : Spec (.of A) ⟶ scheme R M k)
    (ha : a ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Spec (.of A) ⟶ scheme R (⋀[R]^k M) 1 :=
  toSchemeHom (pluckerBaseChange ((schemeHomEquiv R M k A).symm ⟨a, ha⟩))

-- `pluckerAux` depends on the algebra structure on `A` only through its equality class.
private lemma pluckerAux_congr (A : Type u) [CommRing A] (i j : Algebra R A) (h : i = j)
    (a : Spec (.of A) ⟶ scheme R M k) (ha ha') :
    pluckerAux R M k A i a ha = pluckerAux R M k A j a ha' := by
  subst h
  rfl

/-- The morphism of affine points underlying `pluckerHom`: the algebra structure of `A` over `R`
is read off from the composite `Spec A ⟶ G(k, M) ⟶ Spec R`. -/
private noncomputable def pluckerPoint {A : CommRingCat.{u}} (a : Spec A ⟶ scheme R M k) :
    Spec A ⟶ scheme R (⋀[R]^k M) 1 :=
  letI := (Spec.preimage (a ≫ toSpec R M k)).hom.toAlgebra
  pluckerAux R M k A ‹_› a (Spec.map_preimage _).symm

variable {R M k}

/-- `pluckerPoint` computed with any algebra structure on `A` compatible with the morphism. -/
private lemma pluckerPoint_eq (A : Type u) [CommRing A] [Algebra R A]
    (a : Spec (.of A) ⟶ scheme R M k)
    (ha : a ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    pluckerPoint R M k a = pluckerAux R M k A ‹_› a ha := by
  have hφ : (Spec.preimage (a ≫ toSpec R M k)).hom = algebraMap R A := by
    rw [ha, Spec.preimage_map, CommRingCat.hom_ofHom]
  refine pluckerAux_congr R M k A _ _ ?_ a _ _
  exact Algebra.algebra_ext _ _ fun r ↦ DFunLike.congr_fun hφ r

variable {A : Type u} [CommRing A] [Algebra R A]

private lemma pluckerPoint_toSchemeHom (N : G(k, A ⊗[R] M; A)) :
    pluckerPoint R M k (toSchemeHom N) = toSchemeHom (pluckerBaseChange N) := by
  rw [pluckerPoint_eq A _ (toSchemeHom_toSpec N), pluckerAux]
  congr 2
  exact (Equiv.symm_apply_eq _).2 (Subtype.ext (coe_schemeHomEquiv_apply N).symm)

/-- `pluckerPoint` is natural in the affine scheme. -/
private lemma pluckerPoint_comp {B C : CommRingCat.{u}} (ψ : Spec C ⟶ Spec B)
    (a : Spec B ⟶ scheme R M k) :
    pluckerPoint R M k (ψ ≫ a) = ψ ≫ pluckerPoint R M k a := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R M k)
  obtain ⟨χ, rfl⟩ := Spec.map_surjective ψ
  let _ : Algebra R B := φ.hom.toAlgebra
  let _ : Algebra R C := (χ.hom.comp φ.hom).toAlgebra
  let χ' : B →ₐ[R] C := { χ.hom with commutes' := fun _ ↦ rfl }
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
  have h : Spec.map χ ≫ toSchemeHom N = toSchemeHom (map χ' N) := (toSchemeHom_map χ' N).symm
  rw [h, pluckerPoint_toSchemeHom, pluckerPoint_toSchemeHom, pluckerBaseChange_map,
    toSchemeHom_map]
  rfl

variable (R M k) in
/-- **The Plücker morphism** `G(k, M) ⟶ G(1, ⋀ᵏ M)` over `Spec R`: it sends the point classifying
`N ⊆ A ⊗[R] M` over an `R`-algebra `A` to the point classifying the kernel of
`⋀ᵏ (A ⊗[R] M) → ⋀ᵏ ((A ⊗[R] M) ⧸ N)`, read in `A ⊗[R] ⋀ᵏ M`
(`Module.Grassmannian.toSchemeHom_comp_pluckerHom`). -/
noncomputable def pluckerHom : scheme R M k ⟶ scheme R (⋀[R]^k M) 1 :=
  Scheme.homOfAffinePoints (pluckerPoint R M k) pluckerPoint_comp

/-- **`pluckerHom` on points.** The morphism classifying `N` over an `R`-algebra `A`, composed with
`pluckerHom`, classifies the Plücker point of `N`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_pluckerHom (N : G(k, A ⊗[R] M; A)) :
    toSchemeHom N ≫ pluckerHom R M k = toSchemeHom (pluckerBaseChange N) :=
  (Scheme.comp_homOfAffinePoints _ _ _).trans (pluckerPoint_toSchemeHom N)

variable (R M k) in
/-- `pluckerHom` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem pluckerHom_toSpec : pluckerHom R M k ≫ toSpec R (⋀[R]^k M) 1 = toSpec R M k := by
  refine Scheme.hom_ext_of_forall_spec fun B a ↦ ?_
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R M k)
  let _ : Algebra R B := φ.hom.toAlgebra
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
  rw [toSchemeHom_comp_pluckerHom_assoc, toSchemeHom_toSpec, toSchemeHom_toSpec]

end Module.Grassmannian

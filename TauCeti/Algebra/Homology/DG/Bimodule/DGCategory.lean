/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Category
public import TauCeti.Algebra.Homology.DG.Bimodule.Hom.Composition
public import TauCeti.CategoryTheory.DG.HomComplexData
public import TauCeti.CategoryTheory.DG.HomotopyCategory

/-!
# The differential graded category of DG bimodules

DG `(A, B)`-bimodules form a category enriched in cochain complexes. Its homogeneous morphisms
are right-linear cochains with signed left linearity, and its differential is the graded
commutator with the module differentials. Composition in Mathlib's enriched factor order is
`(-1)^(p*q) • (g ∘ f)`. The existing `DGCategoryData.ofKeller` supplies this sign conversion
and the enriched associativity and unit laws.

The closed degree-zero morphisms are exactly the ordinary DG bimodule maps, compatibly with
identities and composition. The construction follows `DGRightModuleCat.homComplexData` and
its closed-morphism comparison, using the signed bimodule subcomplex instead.

As for the right-module enrichment, the ground ring, algebras, and carriers share one universe
because `DGCategory` fixes the universe of its Hom complexes to that of the ground ring. The
ordinary linear category of bimodules allows independent universes.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe u

variable {R A B : Type u} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

namespace DGBimoduleCat

/-! ### The explicit Hom-complex data -/

/-- The explicit Hom-complex data of the DG category of bimodules over `hA` and `hB`:
the Hom complex from `M` to `N` is `TauCeti.dgBimoduleHomComplex`, composition of homogeneous
cochains is composition of the underlying maps, in Keller's order, and the identity is the
identity cochain. -/
noncomputable def homComplexData : DGCategoryData R (DGBimoduleCat.{u, u, u, u} hA hB) :=
  DGCategoryData.ofKeller
    (fun M N => dgBimoduleHomComplex M.isDGBimodule N.isDGBimodule)
    (fun {_ _ _} _ _ _ hqp => LinearMap.mk₂ R (fun g f => dgBimoduleCochains.comp g f hqp)
      (fun _ _ _ => dgBimoduleCochains.add_comp _ _ _ hqp)
      (fun _ _ _ => dgBimoduleCochains.smul_comp _ _ _ hqp)
      (fun _ _ _ => dgBimoduleCochains.comp_add _ _ _ hqp)
      (fun _ _ _ => dgBimoduleCochains.comp_smul _ _ _ hqp))
    (fun M => dgBimoduleCochains.id (B := B) (𝒜 := 𝒜) (ℳ := M.grading))
    (fun {_ _ _ _ _ _} hqp g f => by
      subst hqp
      rw [dgBimoduleHomComplex_d_apply, dgBimoduleHomComplex_d_apply,
        dgBimoduleHomComplex_d_apply]
      exact dgBimoduleCochains.differential_comp g f)
    (fun {_ _ _ _ _ _ _ _ _ _} hrq hqp _ k g f => by
      subst hrq hqp
      exact dgBimoduleCochains.comp_assoc k g f _)
    (fun g => dgBimoduleCochains.comp_id g)
    (fun f => dgBimoduleCochains.id_comp f)

variable (M N P : DGBimoduleCat.{u, u, u, u} hA hB)

/-- The Hom complex of the explicit data is the Hom complex of the two modules. -/
@[simp]
theorem homComplexData_hom :
    (homComplexData (hA := hA) (hB := hB)).hom M N =
      dgBimoduleHomComplex M.isDGBimodule N.isDGBimodule :=
  (rfl)

/-! ### The differential graded category -/

/-- The differential graded category of differential graded bimodules over `hA` and `hB`. -/
noncomputable instance instDGCategory : DGCategory R (DGBimoduleCat.{u, u, u, u} hA hB) :=
  (homComplexData (hA := hA) (hB := hB)).toDGCategory

/-- The Hom complex of the differential graded category of bimodules is the Hom complex of
the two modules. -/
@[simp↓]
theorem dgHomComplex_eq :
    dgHomComplex R M N = dgBimoduleHomComplex M.isDGBimodule N.isDGBimodule :=
  (rfl)

/-- Homogeneous morphisms of the differential graded category, identified with bimodule
cochains through the equality of their Hom complexes. -/
noncomputable def dgHomLinearEquivCochains (n : ℤ) :
    DGHom R n M N ≃ₗ[R]
      dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := M.grading) (𝒩 := N.grading) n :=
  (eqToIso (congrArg (fun K : CochainComplex (ModuleCat R) ℤ => K.X n)
    (dgHomComplex_eq M N))).toLinearEquiv

/-- The identification with cochains acts by transport along the equality of the degree-`n`
terms of the Hom complexes. -/
theorem dgHomLinearEquivCochains_apply (n : ℤ) (f : DGHom R n M N) :
    dgHomLinearEquivCochains M N n f =
      (eqToHom (congrArg (fun K : CochainComplex (ModuleCat R) ℤ => K.X n)
        (dgHomComplex_eq M N))).hom f :=
  Iso.toLinearEquiv_apply _ _

/-- Transported composition in the explicit Hom-complex data is composition of cochains in
reversed order, with the Koszul sign converting Keller's factor order into Mathlib's. -/
@[simp]
theorem homComplexData_comp {p q n : ℤ} (hpq : p + q = n)
    (f : DGHom R p M N) (g : DGHom R q N P) :
    dgHomLinearEquivCochains M P n ((homComplexData (hA := hA) (hB := hB)).comp p q n hpq f g) =
      (p * q).negOnePow • dgBimoduleCochains.comp
        (dgHomLinearEquivCochains N P q g) (dgHomLinearEquivCochains M N p f) (by omega) := by
  simp only [dgHomLinearEquivCochains_apply]
  unfold homComplexData
  -- Abstract the chain-law proofs so the characteristic ofKeller lemma matches the
  -- dependent component carriers.
  generalize_proofs (config := { maxDepth := 0, abstract := false })
  erw [DGCategoryData.ofKeller_comp]
  · exact congrArg (fun c : (dgBimoduleHomComplex M.isDGBimodule P.isDGBimodule).X n =>
        (p * q).negOnePow • c)
      (LinearMap.mk₂_apply R _ g f)
  all_goals assumption

/-- The transported identity of the explicit data is the identity cochain. -/
@[simp]
theorem homComplexData_id :
    dgHomLinearEquivCochains M M 0 ((homComplexData (hA := hA) (hB := hB)).id M) =
      dgBimoduleCochains.id (B := B) (𝒜 := 𝒜) (ℳ := M.grading) := by
  simp only [dgHomLinearEquivCochains_apply]
  unfold homComplexData
  -- Abstract the chain-law proofs so the characteristic ofKeller lemma matches the
  -- dependent component carriers.
  generalize_proofs (config := { maxDepth := 0, abstract := false })
  erw [DGCategoryData.ofKeller_id]
  · erw [eqToHom_refl]
    exact ModuleCat.id_apply _ _
  all_goals assumption

/-- The transported differential of the explicit data is the graded commutator with the module
differentials. -/
@[simp]
theorem homComplexData_d_apply (n : ℤ) (f : DGHom R n M N) :
    dgHomLinearEquivCochains M N (n + 1)
        ((((homComplexData (hA := hA) (hB := hB)).hom M N).d n (n + 1)).hom f) =
      dgBimoduleCochains.differential (hM := M.isDGBimodule) (hN := N.isDGBimodule) n
        (dgHomLinearEquivCochains M N n f) :=
  dgBimoduleHomComplex_d_apply M.isDGBimodule N.isDGBimodule n
    (dgHomLinearEquivCochains M N n f)

/-- The differential of the differential graded category of bimodules is the graded
commutator with the module differentials, after transport to cochains. -/
@[simp↓]
theorem dgDifferential_eq (n : ℤ) (f : DGHom R n M N) :
    dgHomLinearEquivCochains M N (n + 1) (dgDifferential R n f) =
      dgBimoduleCochains.differential (hM := M.isDGBimodule) (hN := N.isDGBimodule) n
        (dgHomLinearEquivCochains M N n f) :=
  (congrArg (dgHomLinearEquivCochains M N (n + 1))
    (DGCategoryData.dgDifferential_toDGCategory (homComplexData (hA := hA) (hB := hB)) n f)).trans
      (homComplexData_d_apply M N n f)

/-- The identity of the differential graded category of bimodules transports to the identity
cochain. -/
@[simp↓]
theorem dgId_eq :
    dgHomLinearEquivCochains M M 0 (dgId R M) =
      dgBimoduleCochains.id (B := B) (𝒜 := 𝒜) (ℳ := M.grading) :=
  (congrArg (dgHomLinearEquivCochains M M 0)
    (DGCategoryData.dgId_toDGCategory (homComplexData (hA := hA) (hB := hB)) M)).trans
      (homComplexData_id M)

/-- Composition in the differential graded category of bimodules is composition of cochains,
carrying the Koszul sign which converts Mathlib's enriched factor order into composition of the
underlying maps, after transport to cochains. -/
@[simp↓]
theorem dgComp_eq {p q n : ℤ} (f : DGHom R p M N) (g : DGHom R q N P) (hpq : p + q = n) :
    dgHomLinearEquivCochains M P n (dgComp R f g hpq) =
      (p * q).negOnePow • dgBimoduleCochains.comp
        (dgHomLinearEquivCochains N P q g) (dgHomLinearEquivCochains M N p f) (by omega) :=
  (congrArg (dgHomLinearEquivCochains M P n)
    (DGCategoryData.dgComp_toDGCategory (homComplexData (hA := hA) (hB := hB)) f g hpq)).trans
      (homComplexData_comp M N P hpq f g)

/-! ### Closed degree-zero morphisms -/

/-- The closed degree-zero morphisms are the preimage of the zero-cocycles of the Hom complex
under the explicit identification with cochains. -/
theorem dgCycles_eq :
    dgCycles R M N = Submodule.comap (dgHomLinearEquivCochains M N 0).toLinearMap
      (LinearMap.ker (dgBimoduleCochains.differential
        (hM := M.isDGBimodule) (hN := N.isDGBimodule) 0)) := by
  ext f
  rw [mem_dgCycles, Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_toLinearMap,
    ← dgDifferential_eq, LinearEquiv.map_eq_zero_iff]

/-- **Morphisms of differential graded bimodules are the closed degree-zero morphisms** of the
differential graded category of bimodules. -/
noncomputable def homLinearEquivDGCycles : (M ⟶ N) ≃ₗ[R] dgCycles R M N :=
  ((dgBimoduleHomLinearEquivZeroCocycles M.isDGBimodule N.isDGBimodule).trans
    ((dgHomLinearEquivCochains M N 0).ofSubmodule' (LinearMap.ker
      (dgBimoduleCochains.differential (hM := M.isDGBimodule)
        (hN := N.isDGBimodule) 0))).symm).trans
    (LinearEquiv.ofEq _ _ (dgCycles_eq M N).symm)

variable {M N P}

/-- The closed degree-zero morphism attached to a morphism of differential graded bimodules
has the same underlying map. -/
@[simp]
theorem coe_homLinearEquivDGCycles_apply (f : M ⟶ N) (x : M) :
    (dgHomLinearEquivCochains M N 0 (homLinearEquivDGCycles M N f)).1.1 x = f x := by
  simp only [homLinearEquivDGCycles, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofSubmodule'_symm_apply, LinearEquiv.apply_symm_apply]
  exact dgBimoduleHomLinearEquivZeroCocycles_apply M.isDGBimodule N.isDGBimodule f x

/-- The morphism of differential graded bimodules attached to a closed degree-zero morphism
has the same underlying map. -/
@[simp]
theorem homLinearEquivDGCycles_symm_apply (f : dgCycles R M N) (x : M) :
    (homLinearEquivDGCycles M N).symm f x =
      (dgHomLinearEquivCochains M N 0 f).1.1 x := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (coe_homLinearEquivDGCycles_apply ((homLinearEquivDGCycles M N).symm f) x).symm

/-- The identity morphism corresponds to the identity of the differential graded category. -/
@[simp]
theorem homLinearEquivDGCycles_id :
    (homLinearEquivDGCycles M M (𝟙 M) : DGHom R 0 M M) = dgId R M := by
  apply (dgHomLinearEquivCochains M M 0).injective
  rw [dgId_eq]
  apply dgBimoduleCochains.ext
  intro x
  rw [coe_homLinearEquivDGCycles_apply, id_apply, dgBimoduleCochains.id_apply]

/-- Composition of morphisms corresponds to composition of closed degree-zero morphisms in the
differential graded category. -/
@[simp]
theorem homLinearEquivDGCycles_comp (f : M ⟶ N) (g : N ⟶ P) :
    homLinearEquivDGCycles M P (f ≫ g) =
      dgCyclesComp R M N P (homLinearEquivDGCycles M N f) (homLinearEquivDGCycles N P g) := by
  apply Subtype.ext
  apply (dgHomLinearEquivCochains M P 0).injective
  rw [coe_dgCyclesComp, dgCompZero_def, dgComp_eq, mul_zero, Int.negOnePow_zero, one_smul]
  apply dgBimoduleCochains.ext
  intro x
  rw [coe_homLinearEquivDGCycles_apply, comp_apply, dgBimoduleCochains.comp_apply,
    coe_homLinearEquivDGCycles_apply, coe_homLinearEquivDGCycles_apply]

end DGBimoduleCat

end TauCeti

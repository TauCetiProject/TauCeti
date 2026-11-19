/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.Algebra.Coalgebra.Comodule.Hochschild.Basic
public import TauCeti.AlgebraicTopology.SimplexCategory.GeneratorsRelations

/-!
# The Hochschild complex of a comodule

Let `H` be a bialgebra over a commutative ring `R` and `M` a right `H`-comodule. The
Hochschild cochains `M ⊗ H ⊗ ⋯ ⊗ H` with their cofaces and codegeneracies form a cosimplicial
`R`-module, and the alternating sum of the cofaces is a differential. The resulting cochain
complex is the Hochschild complex of `M`. Its differential in degree zero is
`m ↦ ρ(m) - m ⊗ 1`, so its cocycles of degree zero are the invariants of `M`.

For the coordinate ring of an affine group scheme `G` this is the complex of functions on
the powers of `G` with values in `M`. The complex is defined for every comodule: neither `M`
nor `H` is assumed flat or finite. For flat `H` its cohomology is the rational cohomology of
`G` with coefficients in `M` (Jantzen, Part I, §4.16); that comparison is not proved here.

The cosimplicial module is assembled as `CategoryTheory.Comonad.simplicialResolution` is: the
cofaces and codegeneracies are lifted through Mathlib's presentation `SimplexCategoryGenRel`
of the simplex category by generators and relations, and the result is precomposed with
`SimplexCategoryGenRel.fromSimplexCategory`. The complex and the vanishing of the square of
its differential come from Mathlib's `AlgebraicTopology.alternatingCofaceMapComplex`.

## Main declarations

* `TauCeti.Comodule.hochschildCosimplicial`: the cosimplicial module of Hochschild cochains.
* `TauCeti.Comodule.hochschildDifferential`: the alternating sum of the cofaces, as a linear
  map.
* `TauCeti.Comodule.hochschildDifferential_comp_hochschildDifferential`: the differential
  squares to zero.
* `TauCeti.Comodule.hochschildComplex`: the Hochschild complex.
* `TauCeti.Comodule.ker_hochschildDifferential_zero`: the cocycles of degree zero are the
  fixed subcomodule.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, Part I, §§4.14–4.16.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable (R : Type u) (H : Type v) (M : Type (max v w))
variable [CommRing R] [Semiring H] [Bialgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]

/-- The Hochschild cochains on the generating cofaces and codegeneracies of the simplex
category. -/
-- Public and exposed because the exposed body of `hochschildCosimplicial` refers to it, so
-- that the terms of the cosimplicial module compute.
@[expose] noncomputable def hochschildQuiver : FreeSimplexQuiver ⥤q ModuleCat.{max v w} R where
  obj n := hochschildCochains R H M n.len
  map f := match f with
    | .δ i => ModuleCat.ofHom (hochschildCoface R H M _ i)
    | .σ i => ModuleCat.ofHom (hochschildCodegeneracy R H M _ i)

/-- The generating cofaces are sent to the Hochschild cofaces. -/
@[simp]
theorem hochschildQuiver_map_δ {n : ℕ} (i : Fin (n + 2)) :
    (hochschildQuiver R H M).map (FreeSimplexQuiver.δ i) =
      ModuleCat.ofHom (hochschildCoface R H M n i) :=
  (rfl)

/-- The generating codegeneracies are sent to the Hochschild codegeneracies. -/
@[simp]
theorem hochschildQuiver_map_σ {n : ℕ} (i : Fin (n + 1)) :
    (hochschildQuiver R H M).map (FreeSimplexQuiver.σ i) =
      ModuleCat.ofHom (hochschildCodegeneracy R H M n i) :=
  (rfl)

/-- The lift of the quiver map to paths agrees with it on generators. -/
private lemma hochschildPaths_map {a b : FreeSimplexQuiver} (f : a ⟶ b) :
    (Paths.lift (hochschildQuiver R H M)).map ((Paths.of _).map f) =
      (hochschildQuiver R H M).map f :=
  Paths.lift_toPath _ f

/-- The cofaces and codegeneracies satisfy the relations presenting the simplex category. -/
private lemma hochschildPaths_respects : ∀ ⦃a b : Paths FreeSimplexQuiver⦄ (f g : a ⟶ b),
    FreeSimplexQuiver.homRel f g →
      (Paths.lift (hochschildQuiver R H M)).map f =
        (Paths.lift (hochschildQuiver R H M)).map g := by
  intro _ _ _ _ h
  cases h
  all_goals simp only [Functor.map_comp, hochschildPaths_map,
    hochschildQuiver_map_δ, hochschildQuiver_map_σ]
  -- Each relation is the image under `ModuleCat.ofHom` of the corresponding identity of
  -- linear maps, since `ModuleCat.ofHom` sends composites and identities to composites and
  -- identities by definition.
  case δ_comp_δ h =>
    exact congrArg ModuleCat.ofHom (hochschildCoface_comp_hochschildCoface R H M h)
  case δ_comp_σ_of_le h =>
    exact congrArg ModuleCat.ofHom (hochschildCodegeneracy_comp_hochschildCoface_of_le R H M h)
  case δ_comp_σ_self i =>
    exact congrArg ModuleCat.ofHom (hochschildCodegeneracy_comp_hochschildCoface_castSucc R H M i)
  case δ_comp_σ_succ i =>
    exact congrArg ModuleCat.ofHom (hochschildCodegeneracy_comp_hochschildCoface_succ R H M i)
  case δ_comp_σ_of_gt h =>
    exact congrArg ModuleCat.ofHom (hochschildCodegeneracy_comp_hochschildCoface_of_gt R H M h)
  case σ_comp_σ h =>
    exact congrArg ModuleCat.ofHom (hochschildCodegeneracy_comp_hochschildCodegeneracy R H M h)

/-- The cosimplicial module of Hochschild cochains of a comodule `M` over a bialgebra `H`:
its term of degree `n` is `M ⊗ H ⊗ ⋯ ⊗ H` with `n` factors `H`. -/
-- Exposed so that its terms unfold to the cochain modules in the statements below.
@[expose] noncomputable def hochschildCosimplicial :
    CosimplicialObject (ModuleCat.{max v w} R) :=
  SimplexCategoryGenRel.fromSimplexCategory ⋙
    CategoryTheory.Quotient.lift _ (Paths.lift (hochschildQuiver R H M))
      (by exact hochschildPaths_respects R H M)

/-- The term of degree `n` of the cosimplicial module is the module of `n`-cochains. -/
@[simp]
theorem hochschildCosimplicial_obj (n : ℕ) :
    (hochschildCosimplicial R H M).obj (SimplexCategory.mk n) = hochschildCochains R H M n :=
  (rfl)

/-- The cofaces of the cosimplicial module are the Hochschild cofaces. -/
@[simp]
theorem hochschildCosimplicial_δ {n : ℕ} (i : Fin (n + 2)) :
    (hochschildCosimplicial R H M).δ i = ModuleCat.ofHom (hochschildCoface R H M n i) :=
  -- `X.δ i` unfolds to `X.map (SimplexCategory.δ i)`, and the map of the composite functor
  -- to the map of the lifted presentation applied to `fromSimplexCategory.map`.
  (congrArg (CategoryTheory.Quotient.lift _ (Paths.lift (hochschildQuiver R H M))
      (hochschildPaths_respects R H M)).map
    (SimplexCategoryGenRel.fromSimplexCategory_map_δ i)).trans <|
    (CategoryTheory.Quotient.lift_map_functor_map ..).trans (hochschildPaths_map R H M (.δ i))

/-- The codegeneracies of the cosimplicial module are the Hochschild codegeneracies. -/
@[simp]
theorem hochschildCosimplicial_σ {n : ℕ} (i : Fin (n + 1)) :
    (hochschildCosimplicial R H M).σ i =
      ModuleCat.ofHom (hochschildCodegeneracy R H M n i) :=
  -- As for the cofaces, `X.σ i` unfolds to the lifted presentation applied to
  -- `fromSimplexCategory.map (SimplexCategory.σ i)`.
  (congrArg (CategoryTheory.Quotient.lift _ (Paths.lift (hochschildQuiver R H M))
      (hochschildPaths_respects R H M)).map
    (SimplexCategoryGenRel.fromSimplexCategory_map_σ i)).trans <|
    (CategoryTheory.Quotient.lift_map_functor_map ..).trans (hochschildPaths_map R H M (.σ i))

/-- The Hochschild differential out of degree `n`: the alternating sum of the `n + 2`
cofaces, starting with the coaction of `M` and ending with the map appending the unit. -/
noncomputable def hochschildDifferential (n : ℕ) :
    hochschildCochains R H M n →ₗ[R] hochschildCochains R H M (n + 1) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • hochschildCoface R H M n i

/-- The Hochschild differential of a cochain is the alternating sum of its cofaces. -/
theorem hochschildDifferential_apply (n : ℕ) (x : hochschildCochains R H M n) :
    hochschildDifferential R H M n x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • hochschildCoface R H M n i x := by
  simp [hochschildDifferential]

/-- The Hochschild complex of a comodule `M` over a bialgebra `H`: the alternating coface
complex of the cosimplicial module of Hochschild cochains. -/
-- Exposed so that its terms unfold to the cochain modules in the statements below.
@[expose] noncomputable def hochschildComplex : CochainComplex (ModuleCat.{max v w} R) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj (hochschildCosimplicial R H M)

/-- The term of degree `n` of the Hochschild complex is the module of `n`-cochains. -/
@[simp]
theorem hochschildComplex_X (n : ℕ) :
    (hochschildComplex R H M).X n = hochschildCochains R H M n :=
  (rfl)

/-- The differential of the Hochschild complex is the Hochschild differential. -/
@[simp]
theorem hochschildComplex_d (n : ℕ) :
    (hochschildComplex R H M).d n (n + 1) =
      ModuleCat.ofHom (hochschildDifferential R H M n) := by
  -- The complex is `CochainComplex.of` applied to Mathlib's alternating sum of the cofaces
  -- of the cosimplicial module, which are the Hochschild cofaces.
  refine (CochainComplex.of_d _ _ n).trans (ModuleCat.hom_ext ((ModuleCat.hom_sum _ _).trans ?_))
  exact Finset.sum_congr rfl fun i _ ↦ (ModuleCat.hom_zsmul _ _).trans
    (congrArg _ (congrArg ModuleCat.Hom.hom (hochschildCosimplicial_δ R H M i)))

/-- The Hochschild differential squares to zero. -/
@[simp]
theorem hochschildDifferential_comp_hochschildDifferential (n : ℕ) :
    hochschildDifferential R H M (n + 1) ∘ₗ hochschildDifferential R H M n = 0 := by
  have h := (hochschildComplex R H M).d_comp_d n (n + 1) (n + 2)
  rw [hochschildComplex_d, hochschildComplex_d] at h
  exact (ModuleCat.hom_comp _ _).symm.trans
    ((congrArg ModuleCat.Hom.hom h).trans ModuleCat.hom_zero)

/-- The Hochschild differential in degree zero is `m ↦ ρ(m) - m ⊗ 1`. -/
theorem hochschildDifferential_zero_apply (m : M) :
    hochschildDifferential R H M 0 m =
      coact (R := R) (C := H) (M := M) m - m ⊗ₜ[R] (1 : H) := by
  rw [hochschildDifferential_apply, Fin.sum_univ_castSucc, Fin.sum_univ_one,
    hochschildCoface_zero_castSucc, hochschildCoface_last_apply]
  simp [sub_eq_add_neg]

/-- On a vector of weight `g`, one with coaction `m ↦ m ⊗ g`, the Hochschild differential in
degree zero is `m ↦ m ⊗ (g - 1)`. -/
theorem hochschildDifferential_zero_apply_of_coact_eq_tmul (H : Type v) [Ring H]
    [Bialgebra R H] [Comodule R H M] {m : M} {g : H}
    (h : coact (R := R) (C := H) (M := M) m = m ⊗ₜ[R] g) :
    hochschildDifferential R H M 0 m = m ⊗ₜ[R] (g - 1) := by
  rw [hochschildDifferential_zero_apply, h, TensorProduct.tmul_sub]

/-- The cocycles of degree zero of the Hochschild complex are the invariants: the kernel of
the differential in degree zero is the fixed subcomodule. -/
theorem ker_hochschildDifferential_zero :
    LinearMap.ker (hochschildDifferential R H M 0) = (fixedSubcomodule R H M).toSubmodule := by
  ext m
  rw [LinearMap.mem_ker, hochschildDifferential_zero_apply, sub_eq_zero,
    Subcomodule.mem_toSubmodule, mem_fixedSubcomodule]

/-- The Hochschild differential in degree one is `x ↦ (ρ ⊗ id) x - (id ⊗ Δ) x + x ⊗ 1`. -/
theorem hochschildDifferential_one_apply (x : M ⊗[R] H) :
    hochschildDifferential R H M 1 x =
      (coact (R := R) (C := H) (M := M)).rTensor H x - cofreeCoact R H M x +
        x ⊗ₜ[R] (1 : H) := by
  rw [hochschildDifferential_apply, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc,
    Fin.sum_univ_one, hochschildCoface_succ_castSucc_castSucc, hochschildCoface_zero_castSucc,
    hochschildCoface_succ_castSucc_last, hochschildCoface_last_apply]
  simp [sub_eq_add_neg]

end TauCeti.Comodule

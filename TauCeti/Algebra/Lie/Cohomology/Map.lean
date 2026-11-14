/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Cochain
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg

/-!
# Functoriality of the Chevalley–Eilenberg complex

A Lie algebra morphism `φ : L' →ₗ⁅R⁆ L` and a linear map of coefficient modules `e : M →ₗ[R] M'`
act on Chevalley–Eilenberg `n`-cochains by pulling arguments back along `φ` and pushing values
forward along `e` (`TauCeti.LieModule.Cohomology.cochainMap`). In degrees one and two, this agrees
with pre- and post-composition of linear maps and with `LieModule.Cohomology.twoCochainMap`.

When `e` intertwines the actions along `φ`, in the sense that `e ⁅φ x, m⁆ = ⁅x, e m⁆` for all
`x : L'` and `m : M` (for instance when both modules carry the trivial action, or when `φ` is the
identity and `e` is a morphism of `L`-modules), `cochainMap` intertwines the Lie derivatives
(`cochainMap_lie`) and therefore commutes with the Chevalley–Eilenberg differential in every degree
(`cochainMap_d`) by induction through Cartan's formula. Within a common module universe, the
degreewise maps assemble into a chain map on `cochainComplex` (`cochainComplexMap`) and induce
functorial maps on Lie algebra cohomology (`cohomologyMap`), contravariant in the Lie algebra and
covariant in the coefficients.

## Main definitions

* `TauCeti.LieModule.Cohomology.cochainMap`: pullback along `φ : L' →ₗ⁅R⁆ L` and coefficient
  pushforward along `e : M →ₗ[R] M'` on `n`-cochains.
* `TauCeti.LieModule.Cohomology.cochainEquiv`: the linear equivalence on `n`-cochains induced by
  a Lie equivalence and a linear equivalence of coefficients.
* `TauCeti.LieModule.Cohomology.cochainComplexMap`: the induced chain map on Chevalley–Eilenberg
  cochain complexes for equivariant `(e, φ)`.
* `TauCeti.LieModule.Cohomology.cohomologyMap`: the induced morphism on degree-`n` cohomology.
* `TauCeti.LieModule.Cohomology.cochainComplexIso`, `TauCeti.LieModule.Cohomology.cohomologyIso`:
  isomorphisms induced by an equivariant pair of equivalences.

## Main results

* `TauCeti.LieModule.Cohomology.cochainMap_lie`: `cochainMap` intertwines Lie derivatives.
* `TauCeti.LieModule.Cohomology.cochainMap_d`: `cochainMap` commutes with the Chevalley–Eilenberg
  differential.
* `TauCeti.LieModule.Cohomology.oneCochainEquiv_cochainMap`,
  `TauCeti.LieModule.Cohomology.twoCochainEquiv_cochainMap`: compatibility with the low-degree
  cochain identifications.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124, §9.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  §7.7.
-/

public section

open AlternatingMap CategoryTheory HomologicalComplex _root_.LieModule.Cohomology

namespace TauCeti.LieModule.Cohomology

universe u v

section CochainMap

variable {R L L' L'' M M' M'' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']
  [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']
  [AddCommGroup M''] [Module R M'']

/-- Pull an `n`-cochain back along a Lie algebra morphism `φ : L' →ₗ⁅R⁆ L` and push its values
forward along a linear map `e : M →ₗ[R] M'`. -/
def cochainMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L) (n : ℕ) :
    (L [⋀^Fin n]→ₗ[R] M) →ₗ[R] (L' [⋀^Fin n]→ₗ[R] M') where
  toFun ω := e.compAlternatingMap (ω.compLinearMap φ.toLinearMap)
  map_add' ω η := by
    ext v
    simp
  map_smul' c ω := by
    ext v
    simp

/-- Evaluating `cochainMap e φ n ω` applies `φ` to each argument and `e` to the resulting value. -/
@[simp]
theorem cochainMap_apply (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L) {n : ℕ}
    (ω : L [⋀^Fin n]→ₗ[R] M) (v : Fin n → L') :
    cochainMap e φ n ω v = e (ω fun i ↦ φ (v i)) :=
  (rfl)

/-- In degree zero, `cochainMap e φ 0` applies `e` to the constant value `ω ![]`. -/
theorem cochainMap_zero_apply (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (ω : L [⋀^Fin 0]→ₗ[R] M) (v : Fin 0 → L') :
    cochainMap e φ 0 ω v = e (ω ![]) := by
  simp [Subsingleton.elim (fun i : Fin 0 ↦ φ (v i)) ![]]

/-- Inserting a first argument `x` into `cochainMap e φ (n + 1) ω` transforms the interior product
`ω.curryLeft (φ x)`. -/
@[simp]
theorem curryLeft_cochainMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L) {n : ℕ}
    (ω : L [⋀^Fin (n + 1)]→ₗ[R] M) (x : L') :
    (cochainMap e φ (n + 1) ω).curryLeft x = cochainMap e φ n (ω.curryLeft (φ x)) := by
  ext v
  simp only [curryLeft_apply_apply, cochainMap_apply]
  congr 2
  ext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

/-- Identity maps on the Lie algebra and coefficients induce the identity on `n`-cochains. -/
@[simp]
theorem cochainMap_id (n : ℕ) :
    cochainMap (LinearMap.id : M →ₗ[R] M) (LieHom.id : L →ₗ⁅R⁆ L) n = LinearMap.id := by
  ext ω v
  simp

/-- `cochainMap` composes covariantly in the coefficients and contravariantly in the Lie
algebra. -/
theorem cochainMap_comp (e : M →ₗ[R] M') (e' : M' →ₗ[R] M'')
    (φ : L' →ₗ⁅R⁆ L) (ψ : L'' →ₗ⁅R⁆ L') (n : ℕ) :
    (cochainMap e' ψ n).comp (cochainMap e φ n) =
      cochainMap (e'.comp e) (φ.comp ψ) n := by
  ext ω v
  simp

/-- Transport of `n`-cochains along a Lie equivalence and a linear equivalence of coefficients. -/
def cochainEquiv (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L) (n : ℕ) :
    (L [⋀^Fin n]→ₗ[R] M) ≃ₗ[R] (L' [⋀^Fin n]→ₗ[R] M') :=
  LinearEquiv.ofLinearMap (cochainMap e.toLinearMap φ.toLieHom n)
    (cochainMap e.symm.toLinearMap φ.symm.toLieHom n)
    (by
      have hp : φ.symm.toLieHom.comp φ.toLieHom = LieHom.id := by ext; simp
      simpa [e.comp_symm, hp] using
        cochainMap_comp e.symm.toLinearMap e.toLinearMap φ.symm.toLieHom φ.toLieHom n)
    (by
      have hp : φ.toLieHom.comp φ.symm.toLieHom = LieHom.id := by ext; simp
      simpa [e.symm_comp, hp] using
        cochainMap_comp e.toLinearMap e.symm.toLinearMap φ.toLieHom φ.symm.toLieHom n)

@[simp]
theorem cochainEquiv_toLinearMap (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L) (n : ℕ) :
    (cochainEquiv e φ n).toLinearMap = cochainMap e.toLinearMap φ.toLieHom n :=
  (rfl)

@[simp]
theorem cochainEquiv_symm_toLinearMap (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L) (n : ℕ) :
    (cochainEquiv e φ n).symm.toLinearMap = cochainMap e.symm.toLinearMap φ.symm.toLieHom n :=
  (rfl)

@[simp]
theorem cochainEquiv_apply (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L) {n : ℕ}
    (ω : L [⋀^Fin n]→ₗ[R] M) :
    cochainEquiv e φ n ω = cochainMap e.toLinearMap φ.toLieHom n ω :=
  (rfl)

@[simp]
theorem cochainEquiv_symm_apply (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L) {n : ℕ}
    (ω : L' [⋀^Fin n]→ₗ[R] M') :
    (cochainEquiv e φ n).symm ω = cochainMap e.symm.toLinearMap φ.symm.toLieHom n ω :=
  (rfl)

/-- In degree one, `cochainMap` corresponds under `oneCochainEquiv` to precomposition with `φ` and
postcomposition with `e`. -/
theorem oneCochainEquiv_cochainMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (ω : L [⋀^Fin 1]→ₗ[R] M) :
    oneCochainEquiv R L' M' (cochainMap e φ 1 ω) =
      e ∘ₗ oneCochainEquiv R L M ω ∘ₗ φ.toLinearMap := by
  ext x
  simp only [oneCochainEquiv_apply, cochainMap_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap]
  congr 2
  ext i
  exact Fin.cases rfl (fun j ↦ j.elim0) i

/-- In degree two, `cochainMap` corresponds under `twoCochainEquiv` to `twoCochainMap`. -/
theorem twoCochainEquiv_cochainMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (ω : L [⋀^Fin 2]→ₗ[R] M) :
    twoCochainEquiv R L' M' (cochainMap e φ 2 ω) =
      twoCochainMap e φ (twoCochainEquiv R L M ω) := by
  refine DFunLike.ext _ _ fun x ↦ LinearMap.ext fun y ↦ ?_
  rw [twoCochainEquiv_apply, cochainMap_apply, twoCochainMap_apply_apply, twoCochainEquiv_apply]
  congr 2
  ext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ k.elim0) j) i

end CochainMap

section Differential

variable {R L L' M M' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']

/-- When `e` intertwines the Lie module actions along `φ`, `cochainMap e φ n` intertwines the Lie
derivatives on `n`-cochains. -/
theorem cochainMap_lie (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (n : ℕ) (x : L')
    (ω : L [⋀^Fin n]→ₗ[R] M) :
    cochainMap e φ n ⁅φ x, ω⁆ = ⁅x, cochainMap e φ n ω⁆ := by
  ext v
  simp only [cochainMap_apply, lie_apply, map_sub, map_sum, he]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ congrArg (e ∘ ω) ?_
  ext j
  rcases eq_or_ne j i with rfl | hji
  · simp only [Function.update_self, LieHom.map_lie]
  · simp only [Function.update_of_ne hji]

/-- **Naturality of the Chevalley–Eilenberg differential.** When `e` intertwines the module
actions along `φ`, `cochainMap` commutes with `d` in every degree. -/
theorem cochainMap_d (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (n : ℕ)
    (ω : L [⋀^Fin n]→ₗ[R] M) :
    cochainMap e φ (n + 1) (d R L M n ω) = d R L' M' n (cochainMap e φ n ω) := by
  induction n with
  | zero =>
    refine curryLeft_injective (LinearMap.ext fun x ↦ ?_)
    rw [curryLeft_cochainMap, curryLeft_d_zero, curryLeft_d_zero, cochainMap_lie e φ he]
  | succ n ih =>
    refine curryLeft_injective (LinearMap.ext fun x ↦ ?_)
    rw [curryLeft_cochainMap, curryLeft_d_succ, map_sub, cochainMap_lie e φ he, ih,
      curryLeft_d_succ, curryLeft_cochainMap]

/-- `cochainMap` commutes with the Chevalley–Eilenberg differential as linear maps. -/
theorem cochainMap_comp_d (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (n : ℕ) :
    (cochainMap e φ (n + 1)).comp (d R L M n) = (d R L' M' n).comp (cochainMap e φ n) :=
  LinearMap.ext (cochainMap_d e φ he n)

omit [LieModule R L M] [LieModule R L' M'] in
/-- If `(e, φ)` is an equivariant pair of equivalences, so is `(e.symm, φ.symm)`. -/
theorem symm_lie_eq_of_lie_eq (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (y : L) (m' : M') :
    e.symm ⁅φ.symm y, m'⁆ = ⁅y, e.symm m'⁆ :=
  e.injective <| by simpa using (he (φ.symm y) (e.symm m')).symm

end Differential

section Complex

variable {R : Type u} [CommRing R]
variable {L L' L'' M M' M'' : Type v}
  [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
  [AddCommGroup M''] [Module R M''] [LieRingModule L'' M''] [LieModule R L'' M'']

/-- The chain map on Chevalley–Eilenberg complexes induced by a Lie algebra morphism
`φ : L' →ₗ⁅R⁆ L` and an intertwining linear map `e : M →ₗ[R] M'`. -/
noncomputable def cochainComplexMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) :
    cochainComplex R L M ⟶ cochainComplex R L' M' :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (cochainMap e φ n)) fun n ↦ by
    rw [cochainComplex_d_succ, cochainComplex_d_succ]
    exact ModuleCat.hom_ext (cochainMap_comp_d e φ he n).symm

/-- In degree `n`, `cochainComplexMap` acts by `cochainMap e φ n`. -/
@[simp]
theorem cochainComplexMap_f (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (n : ℕ) :
    (cochainComplexMap e φ he).f n = ModuleCat.ofHom (cochainMap e φ n) :=
  (rfl)

/-- Identity maps induce the identity chain map on `cochainComplex`. -/
@[simp]
theorem cochainComplexMap_id
    {he : ∀ (x : L) (m : M),
      (LinearMap.id : M →ₗ[R] M) ⁅(LieHom.id : L →ₗ⁅R⁆ L) x, m⁆ = ⁅x, LinearMap.id m⁆} :
    cochainComplexMap (LinearMap.id : M →ₗ[R] M) (LieHom.id : L →ₗ⁅R⁆ L) he =
      𝟙 (cochainComplex R L M) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [cochainComplexMap_f, HomologicalComplex.id_f]
  exact ModuleCat.hom_ext (cochainMap_id n)

/-- `cochainComplexMap` respects composition, covariantly in the coefficients and contravariantly
in the Lie algebra. -/
theorem cochainComplexMap_comp (e : M →ₗ[R] M') (e' : M' →ₗ[R] M'')
    (φ : L' →ₗ⁅R⁆ L) (ψ : L'' →ₗ⁅R⁆ L')
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (he' : ∀ (x : L'') (m' : M'), e' ⁅ψ x, m'⁆ = ⁅x, e' m'⁆) :
    cochainComplexMap e φ he ≫ cochainComplexMap e' ψ he' =
      cochainComplexMap (e'.comp e) (φ.comp ψ)
        (fun x m ↦ by simp [he, he']) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [HomologicalComplex.comp_f, cochainComplexMap_f, cochainComplexMap_f, cochainComplexMap_f]
  exact ModuleCat.hom_ext (cochainMap_comp e e' φ ψ n)

/-- The isomorphism of Chevalley–Eilenberg cochain complexes induced by an equivariant pair of
equivalences. -/
noncomputable def cochainComplexIso (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) :
    cochainComplex R L M ≅ cochainComplex R L' M' where
  hom := cochainComplexMap e.toLinearMap φ.toLieHom he
  inv := cochainComplexMap e.symm.toLinearMap φ.symm.toLieHom (symm_lie_eq_of_lie_eq e φ he)
  hom_inv_id := by
    rw [cochainComplexMap_comp]
    have hp : φ.toLieHom.comp φ.symm.toLieHom = LieHom.id := by ext; simp
    simp [e.symm_comp, hp]
  inv_hom_id := by
    rw [cochainComplexMap_comp]
    have hp : φ.symm.toLieHom.comp φ.toLieHom = LieHom.id := by ext; simp
    simp [e.comp_symm, hp]

@[simp]
theorem cochainComplexIso_hom (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) :
    (cochainComplexIso e φ he).hom = cochainComplexMap e.toLinearMap φ.toLieHom he :=
  (rfl)

@[simp]
theorem cochainComplexIso_inv (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) :
    (cochainComplexIso e φ he).inv =
      cochainComplexMap e.symm.toLinearMap φ.symm.toLieHom (symm_lie_eq_of_lie_eq e φ he) :=
  (rfl)

/-- The morphism on degree-`n` Lie algebra cohomology induced by `φ : L' →ₗ⁅R⁆ L` and an
intertwining linear map `e : M →ₗ[R] M'`. -/
noncomputable def cohomologyMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (n : ℕ) :
    cohomology R L M n ⟶ cohomology R L' M' n :=
  homologyMap (cochainComplexMap e φ he) n

@[simp]
theorem cohomologyMap_id
    {he : ∀ (x : L) (m : M),
      (LinearMap.id : M →ₗ[R] M) ⁅(LieHom.id : L →ₗ⁅R⁆ L) x, m⁆ = ⁅x, LinearMap.id m⁆}
    (n : ℕ) :
    cohomologyMap (LinearMap.id : M →ₗ[R] M) (LieHom.id : L →ₗ⁅R⁆ L) he n =
      𝟙 (cohomology R L M n) := by
  simp [cohomologyMap]

theorem cohomologyMap_comp (e : M →ₗ[R] M') (e' : M' →ₗ[R] M'')
    (φ : L' →ₗ⁅R⁆ L) (ψ : L'' →ₗ⁅R⁆ L')
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (he' : ∀ (x : L'') (m' : M'), e' ⁅ψ x, m'⁆ = ⁅x, e' m'⁆) (n : ℕ) :
    cohomologyMap e φ he n ≫ cohomologyMap e' ψ he' n =
      cohomologyMap (e'.comp e) (φ.comp ψ) (fun x m ↦ by simp [he, he']) n := by
  rw [cohomologyMap, cohomologyMap, ← homologyMap_comp, cochainComplexMap_comp, cohomologyMap]

/-- The isomorphism on degree-`n` Lie algebra cohomology induced by an equivariant pair of
equivalences. -/
noncomputable def cohomologyIso (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (n : ℕ) :
    cohomology R L M n ≅ cohomology R L' M' n :=
  (homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso (cochainComplexIso e φ he)

@[simp]
theorem cohomologyIso_hom (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (n : ℕ) :
    (cohomologyIso e φ he n).hom = cohomologyMap e.toLinearMap φ.toLieHom he n :=
  (rfl)

@[simp]
theorem cohomologyIso_inv (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (n : ℕ) :
    (cohomologyIso e φ he n).inv =
      cohomologyMap e.symm.toLinearMap φ.symm.toLieHom (symm_lie_eq_of_lie_eq e φ he) n :=
  (rfl)

end Complex

end TauCeti.LieModule.Cohomology

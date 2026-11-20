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

Let `f : L' → L` be a morphism of Lie algebras, `M` an `L`-module, `M'` an `L'`-module and
`g : M → M'` a linear map with `g ⁅f x, m⁆ = ⁅x, g m⁆`, that is, a morphism of `L'`-modules from
the pullback of `M` along `f` to `M'`. Pulling cochains back along `f` and pushing them forward
along `g`, `ω ↦ (v ↦ g (ω (f ∘ v)))`, commutes with the Chevalley–Eilenberg differentials
(`d_cochainMap`). It is therefore a morphism of cochain complexes (`cochainComplexMap`), which
induces the maps `H^n(L, M) → H^n(L', M')` on Lie algebra cohomology (`cohomologyMap`). The
construction is contravariant in the Lie algebra and covariant in the coefficients, and respects
identities and composition. In degree two it is the map `twoCochainMap` of 2-cochains
(`twoCochainEquiv_cochainMap`).

Taking `L' = L` and `f` a Lie algebra automorphism gives the action of a group of automorphisms
of `(L, M)` on the cochains, which is how the relative complex of a pair `(𝔤, K)` is cut out.

## Main definitions

* `TauCeti.LieModule.Cohomology.cochainMap`: pullback and pushforward of `n`-cochains.
* `TauCeti.LieModule.Cohomology.cochainComplexMap`: the induced morphism of Chevalley–Eilenberg
  complexes.
* `TauCeti.LieModule.Cohomology.cohomologyMap`: the induced map on Lie algebra cohomology.

## Main results

* `TauCeti.LieModule.Cohomology.d_cochainMap`: pullback and pushforward commute with the
  differential.
* `TauCeti.LieModule.Cohomology.twoCochainEquiv_cochainMap`: in degree two, `cochainMap` is
  `LieModule.Cohomology.twoCochainMap`.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124.
-/

public section

open AlternatingMap CategoryTheory _root_.LieModule.Cohomology

namespace TauCeti.LieModule.Cohomology

universe u v

section Cochains

variable {R L L' L'' M M' M'' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

/-- Pull an `n`-cochain back along a Lie algebra morphism `f` and push it forward along a linear
map `g` of coefficients: `v ↦ g (ω (f ∘ v))`. -/
def cochainMap (g : M →ₗ[R] M') (f : L' →ₗ⁅R⁆ L) (n : ℕ) :
    (L [⋀^Fin n]→ₗ[R] M) →ₗ[R] L' [⋀^Fin n]→ₗ[R] M' where
  toFun ω := (g.compAlternatingMap ω).compLinearMap f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem cochainMap_apply (g : M →ₗ[R] M') (f : L' →ₗ⁅R⁆ L) {n : ℕ}
    (ω : L [⋀^Fin n]→ₗ[R] M) (v : Fin n → L') :
    cochainMap g f n ω v = g (ω fun i ↦ f (v i)) :=
  (rfl)

/-- Pullback and pushforward along identities is the identity. -/
@[simp]
theorem cochainMap_id (n : ℕ) :
    cochainMap (LinearMap.id : M →ₗ[R] M) (LieHom.id : L →ₗ⁅R⁆ L) n = LinearMap.id :=
  LinearMap.ext fun _ ↦ AlternatingMap.ext fun _ ↦ by simp

/-- Pushforward composes covariantly and pullback contravariantly. -/
theorem cochainMap_comp (g : M →ₗ[R] M') (g' : M' →ₗ[R] M'') (f : L' →ₗ⁅R⁆ L)
    (f' : L'' →ₗ⁅R⁆ L') (n : ℕ) :
    cochainMap g' f' n ∘ₗ cochainMap g f n = cochainMap (g' ∘ₗ g) (f.comp f') n :=
  LinearMap.ext fun _ ↦ AlternatingMap.ext fun _ ↦ by simp

/-- In degree two, `cochainMap` is the map `twoCochainMap` of 2-cochains. -/
@[simp]
theorem twoCochainEquiv_cochainMap (g : M →ₗ[R] M') (f : L' →ₗ⁅R⁆ L)
    (ω : L [⋀^Fin 2]→ₗ[R] M) :
    twoCochainEquiv R L' M' (cochainMap g f 2 ω) = twoCochainMap g f (twoCochainEquiv R L M ω) := by
  ext x y
  simp only [twoCochain_val_apply, twoCochainEquiv_apply, twoCochainMap_apply_apply,
    cochainMap_apply]
  congr 2
  ext i
  fin_cases i <;> rfl

/-- In degree two, `cochainMap` is the map `twoCochainMap` of 2-cochains, in terms of the
inverse of `twoCochainEquiv`. -/
theorem cochainMap_twoCochainEquiv_symm (g : M →ₗ[R] M') (f : L' →ₗ⁅R⁆ L)
    (c : twoCochain R L M) :
    cochainMap g f 2 ((twoCochainEquiv R L M).symm c) =
      (twoCochainEquiv R L' M').symm (twoCochainMap g f c) := by
  rw [LinearEquiv.eq_symm_apply, twoCochainEquiv_cochainMap, LinearEquiv.apply_symm_apply]

variable [LieRingModule L M] [LieModule R L M] [LieRingModule L' M'] [LieModule R L' M']

/-- Deleting an entry commutes with applying a function to every entry of a tuple. -/
private theorem removeNth_comp {α β : Type*} (h : α → β) {n : ℕ} (i : Fin (n + 1))
    (v : Fin (n + 1) → α) : (i.removeNth fun k ↦ h (v k)) = fun k ↦ h (i.removeNth v k) :=
  (rfl)

omit [LieModule R L M] [LieModule R L' M'] in
/-- The image under `f` of a tuple with a bracket prepended is the image tuple with the bracket
of the images prepended. -/
private theorem comp_vecCons_lie (f : L' →ₗ⁅R⁆ L) {n : ℕ} (x y : L') (w : Fin n → L') :
    (fun i ↦ f (Matrix.vecCons ⁅x, y⁆ w i)) = Matrix.vecCons ⁅f x, f y⁆ fun i ↦ f (w i) := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

/-- **Naturality of the Chevalley–Eilenberg differential.** If `g ⁅f x, m⁆ = ⁅x, g m⁆`, then
pulling back along `f` and pushing forward along `g` commutes with the differential. -/
theorem d_cochainMap {g : M →ₗ[R] M'} {f : L' →ₗ⁅R⁆ L} (hg : ∀ x m, g ⁅f x, m⁆ = ⁅x, g m⁆)
    {n : ℕ} (ω : L [⋀^Fin n]→ₗ[R] M) :
    d R L' M' n (cochainMap g f n ω) = cochainMap g f (n + 1) (d R L M n ω) := by
  cases n with
  | zero =>
    ext v
    simp only [d_zero_apply, cochainMap_apply, hg]
    congr 3
    exact Subsingleton.elim _ _
  | succ n =>
    ext v
    simp only [d_succ_apply, cochainMap_apply, map_add, map_sum, map_zsmul, hg,
      comp_vecCons_lie, removeNth_comp]

/-- Naturality of the Chevalley–Eilenberg differential, as an identity of linear maps. -/
theorem d_comp_cochainMap {g : M →ₗ[R] M'} {f : L' →ₗ⁅R⁆ L}
    (hg : ∀ x m, g ⁅f x, m⁆ = ⁅x, g m⁆) (n : ℕ) :
    d R L' M' n ∘ₗ cochainMap g f n = cochainMap g f (n + 1) ∘ₗ d R L M n :=
  LinearMap.ext (d_cochainMap hg)

end Cochains

section Complex

variable {R : Type*} {L L' L'' : Type u} {M M' M'' : Type v} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
  [LieRingModule L M] [LieModule R L M] [LieRingModule L' M'] [LieModule R L' M']
  [LieRingModule L'' M''] [LieModule R L'' M'']

/-- The morphism of Chevalley–Eilenberg complexes induced by a Lie algebra morphism `f` and a
compatible map `g` of coefficients. -/
noncomputable def cochainComplexMap {g : M →ₗ[R] M'} {f : L' →ₗ⁅R⁆ L}
    (hg : ∀ x m, g ⁅f x, m⁆ = ⁅x, g m⁆) : cochainComplex R L M ⟶ cochainComplex R L' M' :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (cochainMap g f n)) fun n ↦ by
    rw [cochainComplex_d_succ, cochainComplex_d_succ]
    exact ModuleCat.hom_ext (d_comp_cochainMap hg n)

@[simp]
theorem cochainComplexMap_f {g : M →ₗ[R] M'} {f : L' →ₗ⁅R⁆ L}
    (hg : ∀ x m, g ⁅f x, m⁆ = ⁅x, g m⁆) (n : ℕ) :
    (cochainComplexMap hg).f n = ModuleCat.ofHom (cochainMap g f n) :=
  (rfl)

/-- The map `H^n(L, M) → H^n(L', M')` on Lie algebra cohomology induced by a Lie algebra morphism
`f` and a compatible map `g` of coefficients. -/
noncomputable def cohomologyMap {g : M →ₗ[R] M'} {f : L' →ₗ⁅R⁆ L}
    (hg : ∀ x m, g ⁅f x, m⁆ = ⁅x, g m⁆) (n : ℕ) : cohomology R L M n ⟶ cohomology R L' M' n :=
  HomologicalComplex.homologyMap (cochainComplexMap hg) n

/-- The identity maps induce the identity of the Chevalley–Eilenberg complex. -/
@[simp]
theorem cochainComplexMap_id :
    cochainComplexMap (g := (LinearMap.id : M →ₗ[R] M)) (f := (LieHom.id : L →ₗ⁅R⁆ L))
      (fun _ _ ↦ rfl) = 𝟙 _ := by
  ext n : 2
  rfl

/-- The induced morphisms of Chevalley–Eilenberg complexes compose. -/
theorem cochainComplexMap_comp {g : M →ₗ[R] M'} {g' : M' →ₗ[R] M''} {f : L' →ₗ⁅R⁆ L}
    {f' : L'' →ₗ⁅R⁆ L'} (hg : ∀ x m, g ⁅f x, m⁆ = ⁅x, g m⁆)
    (hg' : ∀ x m, g' ⁅f' x, m⁆ = ⁅x, g' m⁆) :
    cochainComplexMap hg ≫ cochainComplexMap hg' =
      cochainComplexMap (g := g' ∘ₗ g) (f := f.comp f') fun x m ↦ by
        simp [hg, hg'] := by
  ext n : 2
  rfl

/-- The identity maps induce the identity on Lie algebra cohomology. -/
@[simp]
theorem cohomologyMap_id (n : ℕ) :
    cohomologyMap (g := (LinearMap.id : M →ₗ[R] M)) (f := (LieHom.id : L →ₗ⁅R⁆ L))
      (fun _ _ ↦ rfl) n = 𝟙 _ := by
  simp [cohomologyMap]

/-- The induced maps on Lie algebra cohomology compose. -/
theorem cohomologyMap_comp {g : M →ₗ[R] M'} {g' : M' →ₗ[R] M''} {f : L' →ₗ⁅R⁆ L}
    {f' : L'' →ₗ⁅R⁆ L'} (hg : ∀ x m, g ⁅f x, m⁆ = ⁅x, g m⁆)
    (hg' : ∀ x m, g' ⁅f' x, m⁆ = ⁅x, g' m⁆) (n : ℕ) :
    cohomologyMap hg n ≫ cohomologyMap hg' n =
      cohomologyMap (g := g' ∘ₗ g) (f := f.comp f') (fun x m ↦ by simp [hg, hg']) n := by
  rw [cohomologyMap, cohomologyMap, cohomologyMap, ← HomologicalComplex.homologyMap_comp,
    cochainComplexMap_comp]

end Complex

end TauCeti.LieModule.Cohomology

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# The finite adele ring at a single place

Let `R` be a Dedekind domain with fraction field `K`. The finite adele ring `𝔸ᶠ = 𝔸ᶠ[R, K]` is the
restricted product of the completions `K_v = v.adicCompletion K` over the height one primes `v`
of `R`. This file relates `𝔸ᶠ` to one completion `K_v` at a time, in both directions:

* the projection `proj K v : 𝔸ᶠ →A[K] K_v`, reading off the `v`-component, is a continuous
  `K`-algebra homomorphism. It is surjective and open, hence a quotient map, and it carries the
  integral finite adeles onto the local integers `𝒪_v`. That it is a `K`-algebra homomorphism is
  the statement that the diagonal embedding `K → 𝔸ᶠ` followed by the projection is the
  completion map `K → K_v`;
* the map `single K v : K_v →L[K] 𝔸ᶠ` sends `x` to the finite adele with `v`-component `x` and all
  other components `0`. It is a closed embedding onto the finite adeles supported at `v`, it is
  linear over `𝔸ᶠ` acting on `K_v` through the projection, and `single K v x` is integral exactly
  when `x` is.

The multiplicative counterpart of `single K v` is Mathlib's
`IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion`, which puts `1` rather than `0` at the other
places; it is a closed embedding as well.

## Main definitions

* `IsDedekindDomain.FiniteAdeleRing.proj`: the projection onto the completion at a finite place.
* `IsDedekindDomain.FiniteAdeleRing.single`: the finite adeles supported at a single place.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.isOpenQuotientMap_proj`: the projection is an open quotient
  map.
* `IsDedekindDomain.FiniteAdeleRing.image_proj_integralAdeles`: the integral finite adeles project
  onto the local integers.
* `IsDedekindDomain.FiniteAdeleRing.isClosedEmbedding_single` and
  `IsDedekindDomain.FiniteAdeleRing.range_single`: `single K v` is a closed embedding whose range
  is the set of finite adeles vanishing away from `v`;
  `IsDedekindDomain.FiniteAdeleRing.isClosedEmbedding_ofAdicCompletion` is the multiplicative
  counterpart.
* `IsDedekindDomain.FiniteAdeleRing.single_mem_integralAdeles_iff`: a finite adele supported at
  `v` is integral exactly when its `v`-component is.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
* A. Weil, *Basic Number Theory*, Chapter IV, §1.
-/

public section

namespace IsDedekindDomain.FiniteAdeleRing

open HeightOneSpectrum Topology

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-! ### The projection onto one completion -/

variable (K) in
/-- The projection of the finite adele ring onto the completion `v.adicCompletion K` at a finite
place `v`, as a continuous `K`-algebra homomorphism. -/
def proj (v : HeightOneSpectrum R) : FiniteAdeleRing R K →A[K] v.adicCompletion K where
  toFun a := a v
  map_one' := (rfl)
  map_mul' _ _ := (rfl)
  map_zero' := (rfl)
  map_add' _ _ := (rfl)
  -- the `v`-component of the diagonal image of `x` is the image of `x` in the completion
  commutes' _ := (rfl)
  cont := RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum R ↦ w.adicCompletion K)
    (A := fun w ↦ w.adicCompletionIntegers K) v

/-- The projection onto the completion at `v` reads off the `v`-component. -/
@[simp]
theorem proj_apply (v : HeightOneSpectrum R) (a : FiniteAdeleRing R K) : proj K v a = a v :=
  (rfl)

/-! ### Finite adeles supported at one place -/

variable (K) in
/-- The finite adele supported at the single place `v`: its `v`-component is `x` and all its
other components are `0`. It is a continuous `K`-linear map `v.adicCompletion K → 𝔸ᶠ[R, K]`. -/
noncomputable def single (v : HeightOneSpectrum R) :
    v.adicCompletion K →L[K] FiniteAdeleRing R K :=
  letI := Classical.decEq (HeightOneSpectrum R)
  { toFun := RestrictedProduct.single (fun w ↦ w.adicCompletionIntegers K) v
    map_add' := RestrictedProduct.single_add _ v
    map_smul' c x := by
      rw [RingHom.id_apply, Algebra.smul_def c x]
      exact (RestrictedProduct.mul_single _ v x (algebraMap K (FiniteAdeleRing R K) c)).trans
        (Algebra.smul_def (A := FiniteAdeleRing R K) c _).symm
    cont := TauCeti.continuous_restrictedProduct_single _ v }

/-- The finite adele supported at `v` has `v`-component `x`. -/
@[simp]
theorem single_apply_self (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    single K v x v = x := by
  classical
  exact RestrictedProduct.single_eq_same _ v x

/-- The finite adele supported at `v` vanishes at every other place. -/
@[simp]
theorem single_apply_of_ne {v w : HeightOneSpectrum R} (h : w ≠ v) (x : v.adicCompletion K) :
    single K v x w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne _ x h

/-- A finite adele is supported at `v` exactly when it is `single K v` of its `v`-component. -/
theorem eq_single_iff (v : HeightOneSpectrum R) (a : FiniteAdeleRing R K) :
    a = single K v (a v) ↔ ∀ w ≠ v, a w = 0 := by
  refine ⟨fun h w hw ↦ by rw [h, single_apply_of_ne hw], fun h ↦ FiniteAdeleRing.ext K fun w ↦ ?_⟩
  rcases eq_or_ne w v with rfl | hw
  · rw [single_apply_self]
  · rw [single_apply_of_ne hw, h w hw]

/-- The range of `single K v` is the set of finite adeles vanishing at every place other than
`v`. -/
theorem range_single (v : HeightOneSpectrum R) :
    Set.range (single K v) = {a : FiniteAdeleRing R K | ∀ w ≠ v, a w = 0} := by
  ext a
  refine ⟨?_, fun h ↦ ⟨a v, ((eq_single_iff v a).mpr h).symm⟩⟩
  rintro ⟨x, rfl⟩ w hw
  exact single_apply_of_ne hw x

/-- The projection onto the completion at `v` is a left inverse of `single K v`. -/
theorem leftInverse_proj_single (v : HeightOneSpectrum R) :
    Function.LeftInverse (proj K v) (single K v) :=
  single_apply_self v

/-- Multiplying a finite adele supported at `v` by any finite adele `a` multiplies its
`v`-component by `a v`: `single K v` is linear over `𝔸ᶠ[R, K]` acting on the completion through
the projection. -/
@[simp]
theorem mul_single (v : HeightOneSpectrum R) (x : v.adicCompletion K) (a : FiniteAdeleRing R K) :
    single K v (a v * x) = a * single K v x := by
  classical
  exact RestrictedProduct.mul_single _ v x a

/-- The right-handed form of `mul_single`. -/
@[simp]
theorem single_mul (v : HeightOneSpectrum R) (x : v.adicCompletion K) (a : FiniteAdeleRing R K) :
    single K v (x * a v) = single K v x * a := by
  rw [mul_comm x, mul_single, mul_comm]

/-- `single K v` is a closed embedding of the completion at `v` into the finite adele ring. -/
theorem isClosedEmbedding_single (v : HeightOneSpectrum R) :
    IsClosedEmbedding (single K v) := by
  classical
  exact TauCeti.isClosedEmbedding_restrictedProduct_single
    (fun w : HeightOneSpectrum R ↦ w.adicCompletionIntegers K) v

variable (K) in
/-- The finite adele `ofAdicCompletion K v x`, which is `x` at `v` and `1` at every other place,
gives a closed embedding of the completion at `v` into the finite adele ring. -/
theorem isClosedEmbedding_ofAdicCompletion (v : HeightOneSpectrum R) :
    IsClosedEmbedding (ofAdicCompletion K v) := by
  classical
  exact TauCeti.isClosedEmbedding_restrictedProduct_mulSingle
    (fun w : HeightOneSpectrum R ↦ w.adicCompletionIntegers K) v

/-- A finite adele supported at `v` is integral exactly when its `v`-component lies in the local
integers. -/
@[simp]
theorem single_mem_integralAdeles_iff (v : HeightOneSpectrum R) {x : v.adicCompletion K} :
    (∀ w, single K v x w ∈ w.adicCompletionIntegers K) ↔
      x ∈ v.adicCompletionIntegers K := by
  refine ⟨fun h ↦ single_apply_self v x ▸ h v, fun hx w ↦ ?_⟩
  rcases eq_or_ne w v with rfl | hw
  · rwa [single_apply_self]
  · rw [single_apply_of_ne hw]
    exact zero_mem _

/-! ### Topological properties of the projection -/

/-- The projection onto the completion at `v` is surjective. -/
theorem proj_surjective (v : HeightOneSpectrum R) :
    Function.Surjective (proj K v : FiniteAdeleRing R K → v.adicCompletion K) :=
  (leftInverse_proj_single v).surjective

/-- The projection onto the completion at `v` is an open map. -/
theorem isOpenMap_proj (v : HeightOneSpectrum R) :
    IsOpenMap (proj K v : FiniteAdeleRing R K → v.adicCompletion K) :=
  TauCeti.isOpenMap_restrictedProduct_eval (R := fun w : HeightOneSpectrum R ↦ w.adicCompletion K)
    (A := fun w ↦ w.adicCompletionIntegers K) v

/-- The projection onto the completion at `v` is an open quotient map. -/
theorem isOpenQuotientMap_proj (v : HeightOneSpectrum R) :
    IsOpenQuotientMap (proj K v : FiniteAdeleRing R K → v.adicCompletion K) :=
  ⟨proj_surjective v, map_continuous _, isOpenMap_proj v⟩

/-- The integral finite adeles project onto the local integers at `v`. -/
theorem image_proj_integralAdeles (v : HeightOneSpectrum R) :
    proj K v '' (integralAdeles R K : Set (FiniteAdeleRing R K)) = v.adicCompletionIntegers K := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨single K v x,
    mem_integralAdeles.mpr ((single_mem_integralAdeles_iff v).mpr hx), single_apply_self v x⟩⟩
  rintro ⟨a, ha, rfl⟩
  exact mem_integralAdeles.mp ha v

end IsDedekindDomain.FiniteAdeleRing

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Away.Decomposition

/-!
# The finite adele ring split along a finite set of places

Let `R` be a Dedekind domain with fraction field `K` and let `S` be a set of height one primes of
`R`. The finite adele ring away from `S`, `𝔸_{K,f}^S`, is the restricted product of the
completions `K_v` with respect to the local integers `𝒪_v` over the primes `v ∉ S`. It is a
topological `K`-algebra, and forgetting the coordinates at `S` is a continuous `K`-algebra map
`𝔸_{K,f} → 𝔸_{K,f}^S`.

For a finite set `S`, the finite adele ring is the product of the completions at `S` and the
finite adele ring away from `S`:
`𝔸_{K,f} ≃ (∏_{v ∈ S} K_v) × 𝔸_{K,f}^S`, an isomorphism of topological `K`-algebras that is
coordinatewise the identity. It is the additive away decomposition `TauCeti.addAwayDecomposition`
of the restricted product, which is multiplicative and `K`-linear because it does not change any
coordinate, and whose inverse is continuous because the local integers are open.

## Main definitions

* `IsDedekindDomain.FiniteAdeleRing.Away R K S`: the finite adele ring away from `S`.
* `IsDedekindDomain.FiniteAdeleRing.restrictAway K S`: the continuous `K`-algebra map
  `𝔸_{K,f} → 𝔸_{K,f}^S` forgetting the coordinates at `S`.
* `IsDedekindDomain.FiniteAdeleRing.awayEquiv R K hS`: the isomorphism of topological
  `K`-algebras `𝔸_{K,f} ≃ (∏_{v ∈ S} K_v) × 𝔸_{K,f}^S` for a finite set `S`.

## References

* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.2, p. 7.
-/

public section
noncomputable section

open IsDedekindDomain HeightOneSpectrum Filter
open scoped RestrictedProduct

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (S : Set (HeightOneSpectrum R))

/-- The finite adele ring away from a set `S` of finite places, `𝔸_{K,f}^S`: the restricted
product of the completions `K_v` with respect to the local integers `𝒪_v` over the height one
primes `v ∉ S`. No finiteness of `S` is needed to form it. -/
@[expose] def Away : Type _ :=
  Πʳ v : {v : HeightOneSpectrum R // v ∉ S},
    [v.val.adicCompletion K, v.val.adicCompletionIntegers K]

namespace Away

instance instCommRing : CommRing (Away R K S) := inferInstanceAs <| CommRing <|
  Πʳ v : {v : HeightOneSpectrum R // v ∉ S},
    [v.val.adicCompletion K, v.val.adicCompletionIntegers K]

instance instTopologicalSpace : TopologicalSpace (Away R K S) := inferInstanceAs <|
  TopologicalSpace <|
    Πʳ v : {v : HeightOneSpectrum R // v ∉ S},
      [v.val.adicCompletion K, v.val.adicCompletionIntegers K]

instance instIsTopologicalRing : IsTopologicalRing (Away R K S) :=
  haveI : Fact (∀ v : {v : HeightOneSpectrum R // v ∉ S},
      IsOpen (v.val.adicCompletionIntegers K : Set (v.val.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  RestrictedProduct.isTopologicalRing fun v : {v : HeightOneSpectrum R // v ∉ S} ↦
    v.val.adicCompletion K

instance instDFunLike :
    DFunLike (Away R K S) {v : HeightOneSpectrum R // v ∉ S} fun v ↦ v.val.adicCompletion K where
  coe a := a.val
  coe_injective _ _ := Subtype.ext

variable {R K S}

@[ext]
theorem ext {a b : Away R K S} (h : ∀ v, a v = b v) : a = b :=
  Subtype.ext <| funext h

@[simp]
theorem one_apply (v : {v : HeightOneSpectrum R // v ∉ S}) : (1 : Away R K S) v = 1 :=
  (rfl)

@[simp]
theorem zero_apply (v : {v : HeightOneSpectrum R // v ∉ S}) : (0 : Away R K S) v = 0 :=
  (rfl)

@[simp]
theorem neg_apply (a : Away R K S) (v : {v : HeightOneSpectrum R // v ∉ S}) : (-a) v = -a v :=
  (rfl)

@[simp]
theorem add_apply (a b : Away R K S) (v : {v : HeightOneSpectrum R // v ∉ S}) :
    (a + b) v = a v + b v :=
  (rfl)

@[simp]
theorem sub_apply (a b : Away R K S) (v : {v : HeightOneSpectrum R // v ∉ S}) :
    (a - b) v = a v - b v :=
  (rfl)

@[simp]
theorem mul_apply (a b : Away R K S) (v : {v : HeightOneSpectrum R // v ∉ S}) :
    (a * b) v = a v * b v :=
  (rfl)

end Away

/-- Forgetting the coordinates at `S`, as a ring homomorphism. It is upgraded to the continuous
`K`-algebra map `restrictAway` once `Away R K S` carries its `K`-algebra structure. -/
def restrictAwayRingHom : FiniteAdeleRing R K →+* Away R K S :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
    (fun v : {v : HeightOneSpectrum R // v ∉ S} ↦ v.val.adicCompletion K) Subtype.val
    Subtype.val_injective.tendsto_cofinite (fun _ ↦ RingHom.id _) (.of_forall fun _ _ hx ↦ hx)

@[simp]
theorem restrictAwayRingHom_apply (x : FiniteAdeleRing R K)
    (v : {v : HeightOneSpectrum R // v ∉ S}) :
    restrictAwayRingHom R K S x v = x v :=
  (rfl)

/-- The finite adele ring away from `S` is a `K`-algebra through the diagonal embedding of `K`
followed by forgetting the coordinates at `S`. -/
instance Away.instAlgebra : Algebra K (Away R K S) :=
  ((restrictAwayRingHom R K S).comp (algebraMap K (FiniteAdeleRing R K))).toAlgebra

@[simp]
theorem Away.algebraMap_apply (x : K) (v : {v : HeightOneSpectrum R // v ∉ S}) :
    algebraMap K (Away R K S) x v = (x : v.val.adicCompletion K) :=
  (rfl)

variable {R} in
/-- Forgetting the coordinates at `S`: the continuous `K`-algebra map `𝔸_{K,f} → 𝔸_{K,f}^S`. -/
def restrictAway : FiniteAdeleRing R K →A[K] Away R K S where
  __ := restrictAwayRingHom R K S
  commutes' _ := (rfl)
  cont := RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
    (fun v : {v : HeightOneSpectrum R // v ∉ S} ↦ v.val.adicCompletion K) Subtype.val
    Subtype.val_injective.tendsto_cofinite (fun _ ↦ id) (.of_forall fun _ _ hx ↦ hx)
    fun _ ↦ continuous_id

variable {K S} in
@[simp]
theorem restrictAway_apply (x : FiniteAdeleRing R K) (v : {v : HeightOneSpectrum R // v ∉ S}) :
    restrictAway K S x v = x v :=
  (rfl)

/-! ### The splitting along a finite set of places -/

variable {S}

/-- The local integers `𝒪_v ⊆ K_v` as additive subgroups, the reference family of the restricted
product `𝔸_{K,f}`. -/
private abbrev integersAddSubgroup (v : HeightOneSpectrum R) : AddSubgroup (v.adicCompletion K) :=
  (v.adicCompletionIntegers K).toAddSubgroup

/-- The additive away decomposition of the restricted product `𝔸_{K,f}`. -/
private abbrev addDecomposition (hS : S.Finite) :=
  TauCeti.addAwayDecomposition S hS (integersAddSubgroup R K)

private theorem addDecomposition_fst (hS : S.Finite) (x : FiniteAdeleRing R K) (v : S) :
    (addDecomposition R K hS x).1 v = x v :=
  TauCeti.addAwayDecomposition_fst S hS (integersAddSubgroup R K) x v

private theorem addDecomposition_snd (hS : S.Finite) (x : FiniteAdeleRing R K)
    (v : {v : HeightOneSpectrum R // v ∉ S}) :
    (addDecomposition R K hS x).2 v = x v :=
  TauCeti.addAwayDecomposition_snd S hS (integersAddSubgroup R K) x v

/-- For a finite set `S` of finite places, the finite adele ring is the product of the completions
at `S` and the finite adele ring away from `S`, `𝔸_{K,f} ≃ (∏_{v ∈ S} K_v) × 𝔸_{K,f}^S`, as
topological `K`-algebras. Both directions are coordinatewise the identity: `x` goes to
`((x v)_{v ∈ S}, (x v)_{v ∉ S})`. -/
def awayEquiv (hS : S.Finite) :
    FiniteAdeleRing R K ≃A[K] (∀ v : S, v.val.adicCompletion K) × Away R K S where
  toFun x := addDecomposition R K hS x
  invFun y := (addDecomposition R K hS).symm y
  left_inv := (addDecomposition R K hS).left_inv
  right_inv := (addDecomposition R K hS).right_inv
  map_add' := (addDecomposition R K hS).map_add'
  -- `TauCeti.addAwayDecomposition` is stated for `TauCeti.RestrictedProductAddGroup`, of which
  -- `FiniteAdeleRing R K` and `Away R K S` are type synonyms, so `change` restates each component
  -- of the goal at the synonyms, where multiplication is coordinatewise
  -- (`FiniteAdeleRing.mul_apply`).
  map_mul' x y := by
    refine Prod.ext (funext fun v ↦ ?_) (Away.ext fun v ↦ ?_)
    · change (addDecomposition R K hS (x * y)).1 v =
        (addDecomposition R K hS x).1 v * (addDecomposition R K hS y).1 v
      simp only [addDecomposition_fst, FiniteAdeleRing.mul_apply]
    · change (addDecomposition R K hS (x * y)).2 v =
        (addDecomposition R K hS x).2 v * (addDecomposition R K hS y).2 v
      simp only [addDecomposition_snd, FiniteAdeleRing.mul_apply]
  commutes' c := by
    refine Prod.ext (funext fun v ↦ ?_) (Away.ext fun v ↦ ?_)
    · exact addDecomposition_fst R K hS (algebraMap K (FiniteAdeleRing R K) c) v
    · exact addDecomposition_snd R K hS (algebraMap K (FiniteAdeleRing R K) c) v
  continuous_toFun := TauCeti.continuous_addAwayDecomposition S hS (integersAddSubgroup R K)
  continuous_invFun := TauCeti.continuous_addAwayDecomposition_symm S hS
    (integersAddSubgroup R K) fun v _ ↦ Valued.isOpen_valuationSubring _

variable (hS : S.Finite)

/-- The component of `awayEquiv` at a place `v ∈ S` is the coordinate at `v`. -/
@[simp]
theorem awayEquiv_apply_fst (x : FiniteAdeleRing R K) (v : S) :
    (awayEquiv R K hS x).1 v = x v :=
  addDecomposition_fst R K hS x v

/-- The component of `awayEquiv` away from `S` is the restriction `restrictAway`. -/
@[simp]
theorem awayEquiv_apply_snd (x : FiniteAdeleRing R K) :
    (awayEquiv R K hS x).2 = restrictAway K S x :=
  Away.ext fun v ↦ addDecomposition_snd R K hS x v

@[simp]
theorem awayEquiv_symm_apply_of_mem (y : (∀ v : S, v.val.adicCompletion K) × Away R K S)
    (v : HeightOneSpectrum R) (hv : v ∈ S) :
    (awayEquiv R K hS).symm y v = y.1 ⟨v, hv⟩ :=
  TauCeti.addAwayDecomposition_symm_apply_of_mem S hS (integersAddSubgroup R K) y v hv

@[simp]
theorem awayEquiv_symm_apply_of_notMem (y : (∀ v : S, v.val.adicCompletion K) × Away R K S)
    (v : HeightOneSpectrum R) (hv : v ∉ S) :
    (awayEquiv R K hS).symm y v = y.2 ⟨v, hv⟩ :=
  TauCeti.addAwayDecomposition_symm_apply_of_notMem S hS (integersAddSubgroup R K) y v
    hv

end IsDedekindDomain.FiniteAdeleRing

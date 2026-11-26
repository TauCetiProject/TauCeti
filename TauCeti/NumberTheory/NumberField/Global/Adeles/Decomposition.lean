/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Decomposition

/-!
# The adele ring split along a finite set of finite places

Let `R` be a Dedekind domain with fraction field `K` and `S` a finite set of height one primes of
`R`. Mathlib's adele ring `𝔸_K = K_∞ × 𝔸_{K,f}` is the product of the completions at `S` and the
adele ring away from `S`, `𝔸_K^S = K_∞ × 𝔸_{K,f}^S`:
`𝔸_K ≃ (∏_{v ∈ S} K_v) × (K_∞ × 𝔸_{K,f}^S)`, an isomorphism of topological `K`-algebras that is
the identity on the infinite component and the splitting
`IsDedekindDomain.FiniteAdeleRing.awayEquiv` on the finite component.

## Main definitions

* `NumberField.AdeleRing.awayEquiv R K hS`: the isomorphism of topological `K`-algebras
  `𝔸_K ≃ (∏_{v ∈ S} K_v) × (K_∞ × 𝔸_{K,f}^S)`.

## References

* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.2, p. 7.
-/

public section
noncomputable section

open IsDedekindDomain HeightOneSpectrum

namespace NumberField.AdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] {S : Set (HeightOneSpectrum R)}

/-- For a finite set `S` of finite places, the adele ring is the product of the completions at `S`
and the adele ring away from `S`, `𝔸_K ≃ (∏_{v ∈ S} K_v) × (K_∞ × 𝔸_{K,f}^S)`, as topological
`K`-algebras: an adele `(x_∞, x_f)` goes to `((x_f v)_{v ∈ S}, (x_∞, (x_f v)_{v ∉ S}))`. -/
def awayEquiv (hS : S.Finite) :
    AdeleRing R K ≃A[K] (∀ v : S, v.val.adicCompletion K) ×
      (InfiniteAdeleRing K × FiniteAdeleRing.Away R K S) where
  toFun x := ((FiniteAdeleRing.awayEquiv R K hS x.2).1,
    (x.1, (FiniteAdeleRing.awayEquiv R K hS x.2).2))
  invFun y := (y.2.1, (FiniteAdeleRing.awayEquiv R K hS).symm (y.1, y.2.2))
  left_inv x := by simp [-FiniteAdeleRing.awayEquiv_apply_snd]
  right_inv y := by simp
  -- `AdeleRing R K` is a type synonym of the product, so the components of a sum or a product of
  -- adeles are the sums or products of the components only by definition
  map_add' x y := by
    have h := map_add (FiniteAdeleRing.awayEquiv R K hS) x.2 y.2
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    exacts [(congrArg Prod.fst h :), (congrArg Prod.snd h :)]
  map_mul' x y := by
    have h := map_mul (FiniteAdeleRing.awayEquiv R K hS) x.2 y.2
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    exacts [(congrArg Prod.fst h :), (congrArg Prod.snd h :)]
  commutes' c := by
    have h := AlgEquiv.commutes (FiniteAdeleRing.awayEquiv R K hS).toAlgEquiv c
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    exacts [(congrArg Prod.fst h :), (congrArg Prod.snd h :)]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable {R K} (hS : S.Finite)

@[simp]
theorem awayEquiv_apply (x : AdeleRing R K) :
    awayEquiv R K hS x = ((FiniteAdeleRing.awayEquiv R K hS x.2).1,
      (x.1, FiniteAdeleRing.restrictAway K S x.2)) := by
  simp [awayEquiv]

@[simp]
theorem awayEquiv_symm_apply
    (y : (∀ v : S, v.val.adicCompletion K) ×
      (InfiniteAdeleRing K × FiniteAdeleRing.Away R K S)) :
    (awayEquiv R K hS).symm y = (y.2.1, (FiniteAdeleRing.awayEquiv R K hS).symm (y.1, y.2.2)) :=
  (rfl)

end NumberField.AdeleRing

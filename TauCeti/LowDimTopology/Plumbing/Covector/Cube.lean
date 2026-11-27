/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import TauCeti.LowDimTopology.Plumbing.Differential
public import TauCeti.LowDimTopology.Plumbing.SpinC
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Finsupp.Span
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import TauCeti.LowDimTopology.Plumbing.Cube.Face.Translation
import TauCeti.LowDimTopology.Plumbing.OneVertex

/-!
# The lattice complex on characteristic covectors

Let `P` be a plumbing graph with intersection form `A`. Besides Némethi's complex of the lattice
`V → ℤ` for one characteristic covector `k` (`TauCeti.PlumbingGraph.latticeDifferential`), lattice
homology has a second model, used by Zemke, in which the characteristic covector varies and the
cubes sit at the origin. It is generated over `𝔽₂[U]` by
the pairs `[K, E]` of a characteristic covector `K` and a finite set `E` of vertices
(`TauCeti.PlumbingGraph.CovectorCube`). For `I ⊆ E` write `E_I = ∑_{v ∈ I} E_v` and

`f_K(I) = (K(E_I) + E_I · E_I) / 2`,  `g(K, E) = min_{I ⊆ E} f_K(I)`,

`A_v(K, E) = g(K, E ∖ v)`,  `B_v(K, E) = min_{v ∈ I ⊆ E} f_K(I)`.

The differential is

`∂ [K, E] = ∑_{v ∈ E} (U ^ (A_v - g) [K, E ∖ v] + U ^ (B_v - g) [K + 2 v*, E ∖ v])`,

where `v* = A E_v` is the covector dual to the vertex `v`
(`TauCeti.PlumbingGraph.covectorDifferential`). Since `f_K(I) = -χ_K(E_I)` for Némethi's weight
`χ_K`, the minimum `g(K, E)` is minus the weight of the cube of the lattice based at the origin
with directions `E`, and `A_v - g` and `B_v - g` are the exponents of its lower and upper faces in
direction `v`. The definition below uses those exponents
(`TauCeti.PlumbingGraph.characteristicLowerFaceExponent`,
`TauCeti.PlumbingGraph.characteristicUpperFaceExponent`), so both are natural numbers by
construction, and at least one of them vanishes in each direction
(`TauCeti.PlumbingCube.min_characteristicFaceExponent_eq_zero`).

The two models are compared by translation. Shifting a characteristic covector by `2 A m`
translates the weight function by `m` up to a constant,
`χ_{k + 2 A m}(y) = χ_k(y + m) - χ_k(m)`, so the cube weights and their face exponents are
translation invariant (`TauCeti.PlumbingGraph.characteristicCubeWeight_addTwoMulVec_eq_sub`, for
the shift `TauCeti.PlumbingGraph.addTwoMulVec`). Hence sending the cube `(x, E)` of the complex of
`k` to the generator `[k + 2 A x, E]` is a chain map
(`TauCeti.PlumbingGraph.covectorDifferential_comp_toCovectorChain`). Every generator `[K, E]` is
the image of the cube `(0, E)` under the map for `K`, so the relation `∂ ∘ ∂ = 0` of Némethi's
complex gives the same relation here (`TauCeti.PlumbingGraph.covectorDifferential_comp_self`).

The differential preserves the classes of the covectors modulo `2 A (V → ℤ)`
(`TauCeti.PlumbingGraph.characteristicOrbits`), and the chain map for `k` has as image exactly the
chains supported on the orbit of `k` (`TauCeti.PlumbingGraph.range_toCovectorChain`). When
`det A ≠ 0`, for instance for a negative-definite plumbing
(`TauCeti.PlumbingGraph.IsNegativeDefinite.det_intersectionMatrix_ne_zero`), the chain map is
injective, so the summand of an orbit is isomorphic to Némethi's complex of any representative
(`TauCeti.PlumbingGraph.latticeChainEquivCovectorOrbitPart`).
For a degenerate form the two models differ: on the vertex with framing `0` the vector `v*`
vanishes, the two faces of `[0, {v}]` coincide and cancel, and `[0, {v}]` is a cycle.

## Main definitions

* `TauCeti.PlumbingGraph.CovectorCube`: a generator `[K, E]`.
* `TauCeti.PlumbingGraph.CovectorChain`: the free `𝔽₂[U]`-module on the generators.
* `TauCeti.PlumbingGraph.covectorDifferential`: the differential.
* `TauCeti.PlumbingGraph.toCovectorChain`: the map `(x, E) ↦ [k + 2 A x, E]` from Némethi's
  complex of `k`.
* `TauCeti.PlumbingGraph.covectorOrbitPart`: the summand of the chains supported on one orbit.
* `TauCeti.PlumbingGraph.latticeChainEquivCovectorOrbitPart`: for `det A ≠ 0`, the isomorphism
  of Némethi's complex of `k` with the summand of the orbit of `k`.

## Main results

* `TauCeti.PlumbingGraph.covectorDifferential_comp_toCovectorChain`: the comparison map is a
  chain map.
* `TauCeti.PlumbingGraph.covectorDifferential_comp_self`: `∂ ∘ ∂ = 0`.
* `TauCeti.PlumbingGraph.covectorDifferential_single_mk_singleton`: the differential of a
  one-dimensional generator, with exponents `max(0, -f_K(v))` and `max(0, f_K(v))`.
* `TauCeti.PlumbingGraph.covectorDifferential_mem_covectorOrbitPart`: the differential preserves
  the summand of each orbit.
* `TauCeti.PlumbingGraph.range_toCovectorChain`,
  `TauCeti.PlumbingGraph.toCovectorChain_injective`: the image of the comparison map is the
  summand of an orbit, and the map is injective when `det A ≠ 0`.

## References

* I. Zemke, *The equivalence of lattice and Heegaard Floer homology*,
  [arXiv:2111.14962](https://arxiv.org/abs/2111.14962), §2.3 (the complex on the generators
  `[K, E]`, the quantities `f_K`, `g`, `A_v`, `B_v` and the differential).
* A. Némethi, *Lattice cohomology of normal surface singularities*,
  [arXiv:0709.0841](https://arxiv.org/abs/0709.0841), §3 (the weight function and the complex of
  one characteristic covector).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-! ### Generators and the differential -/

omit [DecidableEq V] [Fintype V] in
/-- A generator `[K, E]` of the lattice complex on characteristic covectors: a characteristic
covector `K` together with a finite set `E` of vertices. It plays the role of the cube of the
lattice based at the origin with directions `E`, read with the covector `K`. -/
@[ext]
structure CovectorCube where
  /-- The characteristic covector `K`. -/
  covector : P.characteristicVectors
  /-- The set `E` of vertices, the directions of the cube. -/
  directions : Finset V

omit [DecidableEq V] [Fintype V] in
/-- The free `𝔽₂[U]`-module on the generators `[K, E]`. -/
abbrev CovectorChain : Type _ := P.CovectorCube →₀ PlumbingCoefficient

/-- The differential of one generator `[K, E]`: for each `v ∈ E`, the face `[K, E ∖ v]` with the
lower-face exponent and the face `[K + 2 A E_v, E ∖ v]` with the upper-face exponent of the cube
based at the origin with directions `E`, for the covector `K`. -/
noncomputable def covectorDifferentialOnGenerator (C : P.CovectorCube) : P.CovectorChain :=
  C.directions.attach.sum fun v =>
    Finsupp.single ⟨C.covector, C.directions.erase v⟩
        (Polynomial.X ^ P.characteristicLowerFaceExponent C.covector 0 C.directions v) +
      Finsupp.single
        ⟨P.addTwoMulVec C.covector (Pi.single v 1), C.directions.erase v⟩
        (Polynomial.X ^ P.characteristicUpperFaceExponent C.covector 0 C.directions v.property)

/-- The differential of a generator, written with its covector `K` and its directions `E`. -/
theorem covectorDifferentialOnGenerator_mk (K : P.characteristicVectors) (E : Finset V) :
    P.covectorDifferentialOnGenerator ⟨K, E⟩ =
      E.attach.sum fun v =>
        Finsupp.single ⟨K, E.erase v⟩
            (Polynomial.X ^ P.characteristicLowerFaceExponent K 0 E v) +
          Finsupp.single
            ⟨P.addTwoMulVec K (Pi.single v 1), E.erase v⟩
            (Polynomial.X ^ P.characteristicUpperFaceExponent K 0 E v.property) :=
  (rfl)

/-- The `𝔽₂[U]`-linear differential of the lattice complex on characteristic covectors. -/
noncomputable def covectorDifferential :
    P.CovectorChain →ₗ[PlumbingCoefficient] P.CovectorChain :=
  Finsupp.linearCombination PlumbingCoefficient P.covectorDifferentialOnGenerator

/-- The differential sends a generator with coefficient `a` to `a` times its differential. -/
@[simp]
theorem covectorDifferential_single (C : P.CovectorCube) (a : PlumbingCoefficient) :
    P.covectorDifferential (Finsupp.single C a) = a • P.covectorDifferentialOnGenerator C :=
  Finsupp.linearCombination_single _ _ _

/-- The component at `D` of the differential of a finitely supported chain is a sum over any finite
set containing the generators whose differential involves `D`. -/
theorem covectorDifferential_apply_eq_sum (x : P.CovectorChain) (D : P.CovectorCube)
    {s : Finset P.CovectorCube}
    (hs : ∀ C, P.covectorDifferentialOnGenerator C D ≠ 0 → C ∈ s) :
    P.covectorDifferential x D = ∑ C ∈ s, x C * P.covectorDifferentialOnGenerator C D := by
  classical
  conv_lhs => rw [← Finsupp.sum_single x]
  rw [map_finsuppSum, Finsupp.sum, Finsupp.finsetSum_apply]
  simp only [covectorDifferential_single, Finsupp.smul_apply, smul_eq_mul]
  have h₁ : ∑ C ∈ x.support, x C * P.covectorDifferentialOnGenerator C D =
      ∑ C ∈ x.support ∪ s, x C * P.covectorDifferentialOnGenerator C D :=
    Finset.sum_subset Finset.subset_union_left fun C _ hC => by
      rw [Finsupp.notMem_support_iff.mp hC, zero_mul]
  have h₂ : ∑ C ∈ s, x C * P.covectorDifferentialOnGenerator C D =
      ∑ C ∈ x.support ∪ s, x C * P.covectorDifferentialOnGenerator C D :=
    Finset.sum_subset Finset.subset_union_right fun C _ hC => by
      rw [not_not.mp (mt (hs C) hC), mul_zero]
  rw [h₁, h₂]

/-! ### Comparison with Némethi's complex -/

/-- The generator `[k + 2 A x, E]` attached to the cube `(x, E)` of Némethi's complex of `k`. -/
def toCovectorCube (k : P.characteristicVectors) (C : PlumbingCube V) : P.CovectorCube :=
  ⟨P.addTwoMulVec k C.base, C.directions⟩

/-- The generator attached to the cube `(x, E)` is `[k + 2 A x, E]`. -/
@[simp]
theorem toCovectorCube_mk (k : P.characteristicVectors) (x : V → ℤ) (E : Finset V) :
    P.toCovectorCube k ⟨x, E⟩ = ⟨P.addTwoMulVec k x, E⟩ :=
  (rfl)

/-- The generator attached to the cube `(0, E)` is `[k, E]`. -/
theorem toCovectorCube_zero (k : P.characteristicVectors) (E : Finset V) :
    P.toCovectorCube k ⟨0, E⟩ = ⟨k, E⟩ := by
  ext v <;> simp

/-- The comparison map from Némethi's complex of `k`, sending the cube `(x, E)` to the generator
`[k + 2 A x, E]`. -/
noncomputable def toCovectorChain (k : P.characteristicVectors) :
    PlumbingChain V →ₗ[PlumbingCoefficient] P.CovectorChain :=
  Finsupp.lmapDomain PlumbingCoefficient PlumbingCoefficient (P.toCovectorCube k)

/-- The comparison map on a single cube. -/
@[simp]
theorem toCovectorChain_single (k : P.characteristicVectors) (C : PlumbingCube V)
    (a : PlumbingCoefficient) :
    P.toCovectorChain k (Finsupp.single C a) = Finsupp.single (P.toCovectorCube k C) a := by
  rw [toCovectorChain, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The comparison map intertwines the two differentials on a single cube. -/
theorem covectorDifferential_toCovectorChain_single (k : P.characteristicVectors)
    (C : PlumbingCube V) :
    P.covectorDifferential (P.toCovectorChain k (Finsupp.single C 1)) =
      P.toCovectorChain k (P.latticeDifferential k (Finsupp.single C 1)) := by
  obtain ⟨x, S⟩ := C
  simp [covectorDifferentialOnGenerator_mk, latticeDifferentialOnGenerator_def,
    characteristicLowerFaceExponent_addTwoMulVec, characteristicUpperFaceExponent_addTwoMulVec]

/-- **The comparison map is a chain map**: sending the cube `(x, E)` of Némethi's complex of `k`
to the generator `[k + 2 A x, E]` intertwines Némethi's differential with the differential on
characteristic covectors. -/
theorem covectorDifferential_comp_toCovectorChain (k : P.characteristicVectors) :
    P.covectorDifferential ∘ₗ P.toCovectorChain k =
      P.toCovectorChain k ∘ₗ P.latticeDifferential k :=
  Finsupp.lhom_ext' fun C => LinearMap.ext_ring
    (P.covectorDifferential_toCovectorChain_single k C)

/-- The comparison map intertwines the two differentials. -/
theorem covectorDifferential_toCovectorChain (k : P.characteristicVectors) (c : PlumbingChain V) :
    P.covectorDifferential (P.toCovectorChain k c) =
      P.toCovectorChain k (P.latticeDifferential k c) :=
  LinearMap.congr_fun (P.covectorDifferential_comp_toCovectorChain k) c

/-- **The differential squares to zero.** The generator `[K, E]` is the image of the cube
`(0, E)` under the comparison chain map for `K`, so this is inherited from Némethi's complex. -/
theorem covectorDifferential_comp_self :
    P.covectorDifferential ∘ₗ P.covectorDifferential = 0 := by
  refine Finsupp.lhom_ext' fun C => LinearMap.ext_ring ?_
  obtain ⟨K, E⟩ := C
  have h : Finsupp.single (⟨K, E⟩ : P.CovectorCube) (1 : PlumbingCoefficient) =
      P.toCovectorChain K (Finsupp.single ⟨0, E⟩ 1) := by
    rw [toCovectorChain_single, toCovectorCube_zero]
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply, h,
    covectorDifferential_toCovectorChain]
  rw [← LinearMap.comp_apply (P.latticeDifferential K), latticeDifferential_comp_self,
    LinearMap.zero_apply, map_zero]

/-- The differential of the differential of any chain vanishes. -/
@[simp]
theorem covectorDifferential_covectorDifferential (c : P.CovectorChain) :
    P.covectorDifferential (P.covectorDifferential c) = 0 :=
  LinearMap.congr_fun P.covectorDifferential_comp_self c

/-! ### One-dimensional generators -/

/-- **The differential of a one-dimensional generator.** Writing `f_K(v) = (K(v) + v · v) / 2`,
the differential of `[K, {v}]` is `U ^ max(0, -f_K(v)) [K, ∅] + U ^ max(0, f_K(v)) [K + 2 v*, ∅]`.
Since `f_K(∅) = 0`, these exponents are `A_v - g` and `B_v - g` for `g = min(0, f_K(v))`. -/
theorem covectorDifferential_single_mk_singleton (K : P.characteristicVectors) (v : V) :
    P.covectorDifferential (Finsupp.single ⟨K, {v}⟩ 1) =
      Finsupp.single ⟨K, ∅⟩ (Polynomial.X ^ (-((K.val v + P.weight v) / 2)).toNat) +
        Finsupp.single
          ⟨P.addTwoMulVec K (Pi.single v 1), ∅⟩
          (Polynomial.X ^ ((K.val v + P.weight v) / 2).toNat) := by
  have hlower : (max 0 (-((K.val v + P.weight v) / 2))).toNat =
      (-((K.val v + P.weight v) / 2)).toNat := by omega
  have hupper : (max 0 (-((K.val v + P.weight v) / 2)) + (K.val v + P.weight v) / 2).toNat =
      ((K.val v + P.weight v) / 2).toNat := by omega
  simp [covectorDifferentialOnGenerator_mk, ← Finset.univ_eq_attach, characteristicWeight_single,
    hlower, hupper]

/-! ### Orbits of characteristic covectors -/

/-- The summand of the chains supported on the generators `[K, E]` whose covector `K` lies in the
orbit `o`, modulo `2 A (V → ℤ)`. -/
noncomputable def covectorOrbitPart (o : P.characteristicOrbits) :
    Submodule PlumbingCoefficient P.CovectorChain :=
  Finsupp.supported PlumbingCoefficient PlumbingCoefficient
    {C : P.CovectorCube | P.characteristicOrbit C.covector = o}

/-- Membership in the summand of an orbit: every generator in the support has its covector in the
orbit. -/
theorem mem_covectorOrbitPart_iff {o : P.characteristicOrbits} {c : P.CovectorChain} :
    c ∈ P.covectorOrbitPart o ↔ ∀ C ∈ c.support, P.characteristicOrbit C.covector = o :=
  Finsupp.mem_supported' _ _ |>.trans <| by
    simp only [Set.mem_ofPred_eq, Finsupp.mem_support_iff]
    exact forall_congr' fun C => not_imp_comm

/-- **The image of the comparison map is the summand of an orbit**: the chains in the image of the
comparison map for `k` are exactly those supported on the generators whose covector lies in the
orbit of `k`. -/
theorem range_toCovectorChain (k : P.characteristicVectors) :
    LinearMap.range (P.toCovectorChain k) = P.covectorOrbitPart (P.characteristicOrbit k) := by
  have hrange : Set.range (P.toCovectorCube k) =
      {C : P.CovectorCube | P.characteristicOrbit C.covector = P.characteristicOrbit k} := by
    ext ⟨K, E⟩
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨x, S⟩, h⟩
      rw [toCovectorCube_mk, CovectorCube.mk.injEq] at h
      rw [← h.1, characteristicOrbit_addTwoMulVec]
    · intro h
      obtain ⟨x, rfl⟩ := (P.isSpinCEquivalent_iff k K).mp
        (IsSpinCEquivalent.symm P ((P.characteristicOrbit_eq_iff K k).mp h))
      exact ⟨⟨x, E⟩, P.toCovectorCube_mk k x E⟩
  rw [toCovectorChain, Finsupp.range_lmapDomain, covectorOrbitPart, ← hrange,
    Finsupp.supported_eq_span_single, ← Set.range_comp, Function.comp_def]

/-- The differential preserves the summand of each orbit. -/
theorem covectorDifferential_mem_covectorOrbitPart {o : P.characteristicOrbits}
    {c : P.CovectorChain} (hc : c ∈ P.covectorOrbitPart o) :
    P.covectorDifferential c ∈ P.covectorOrbitPart o := by
  obtain ⟨k, rfl⟩ := P.characteristicOrbit_surjective o
  rw [← range_toCovectorChain] at hc ⊢
  obtain ⟨b, rfl⟩ := hc
  exact ⟨P.latticeDifferential k b, (P.covectorDifferential_toCovectorChain k b).symm⟩

/-- **The comparison map is injective for a nondegenerate form.** When `det A ≠ 0`, distinct
lattice points `x` give distinct covectors `k + 2 A x`. -/
theorem toCovectorChain_injective (k : P.characteristicVectors)
    (h : P.intersectionMatrix.det ≠ 0) : Function.Injective (P.toCovectorChain k) := by
  refine Finsupp.mapDomain_injective fun C D hCD => ?_
  obtain ⟨x, S⟩ := C
  obtain ⟨y, T⟩ := D
  rw [toCovectorCube_mk, toCovectorCube_mk, CovectorCube.mk.injEq, Subtype.ext_iff] at hCD
  refine PlumbingCube.ext (Matrix.mulVec_injective_of_det_ne_zero h (funext fun v => ?_)) hCD.2
  have := congr_fun hCD.1 v
  simp only [addTwoMulVec_val] at this ⊢
  omega

/-- **Némethi's complex of `k` is the summand of the orbit of `k`** when `det A ≠ 0`: the
comparison map identifies the free module on the cubes of the lattice with the chains supported on
the generators whose covector lies in the orbit of `k`
(`TauCeti.PlumbingGraph.coe_latticeChainEquivCovectorOrbitPart_apply`). By
`covectorDifferential_toCovectorChain` it intertwines the two differentials. -/
noncomputable def latticeChainEquivCovectorOrbitPart (k : P.characteristicVectors)
    (h : P.intersectionMatrix.det ≠ 0) :
    PlumbingChain V ≃ₗ[PlumbingCoefficient] P.covectorOrbitPart (P.characteristicOrbit k) :=
  (LinearEquiv.ofInjective _ (P.toCovectorChain_injective k h)).trans
    (LinearEquiv.ofEq _ _ (P.range_toCovectorChain k))

/-- The isomorphism of `latticeChainEquivCovectorOrbitPart` is the comparison map. -/
@[simp]
theorem coe_latticeChainEquivCovectorOrbitPart_apply (k : P.characteristicVectors)
    (h : P.intersectionMatrix.det ≠ 0) (c : PlumbingChain V) :
    (P.latticeChainEquivCovectorOrbitPart k h c : P.CovectorChain) = P.toCovectorChain k c := by
  simp [latticeChainEquivCovectorOrbitPart, LinearEquiv.ofInjective_apply,
    LinearEquiv.coe_ofEq_apply]

end PlumbingGraph

/-! ### Examples -/

/-- On the vertex with framing `-1` and the covector `K(v) = -1`, where `f_K(v) = -1`, the
differential of `[K, {v}]` is `U [K, ∅] + [K - 2, ∅]`: the lower face carries the exponent `1`
and the upper face the exponent `0`. -/
example :
    (oneVertexPlumbing (-1)).covectorDifferential
        (Finsupp.single ⟨⟨fun _ => -1, (PlumbingGraph.isCharacteristicVector_iff _ _).mpr
          fun _ => by simp [Int.ModEq]⟩, {0}⟩ 1) =
      Finsupp.single ⟨⟨fun _ => -1, (PlumbingGraph.isCharacteristicVector_iff _ _).mpr
          fun _ => by simp [Int.ModEq]⟩, ∅⟩ Polynomial.X +
        Finsupp.single ⟨⟨fun _ => -3, (PlumbingGraph.isCharacteristicVector_iff _ _).mpr
          fun _ => by simp [Int.ModEq]⟩, ∅⟩ 1 := by
  rw [PlumbingGraph.covectorDifferential_single_mk_singleton]
  congr 2
  · norm_num
  · rw [PlumbingGraph.CovectorCube.mk.injEq]
    refine ⟨Subtype.ext (funext fun i => ?_), rfl⟩
    fin_cases i
    simp
  · norm_num

/-- On the vertex with framing `0` the dual vector `v*` vanishes, so the two faces of `[0, {v}]`
are both `[0, ∅]`, with exponent `0`, and cancel over `𝔽₂`: `[0, {v}]` is a cycle. -/
example :
    (oneVertexPlumbing 0).covectorDifferential
        (Finsupp.single ⟨⟨0, (PlumbingGraph.isCharacteristicVector_iff _ _).mpr
          fun _ => by simp [Int.ModEq]⟩, {0}⟩ 1) = 0 := by
  have hA : (oneVertexPlumbing 0).intersectionMatrix = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have key (c : (oneVertexPlumbing 0).CovectorCube) :
      Finsupp.single c (1 : PlumbingCoefficient) + Finsupp.single c 1 = 0 := by
    rw [← Finsupp.single_add, CharTwo.add_self_eq_zero, Finsupp.single_zero]
  rw [PlumbingGraph.covectorDifferential_single_mk_singleton]
  convert key _ using 3
  · simp
  · rw [PlumbingGraph.CovectorCube.mk.injEq]
    exact ⟨Subtype.ext (funext fun i => by simp [hA]), rfl⟩
  · simp

end TauCeti

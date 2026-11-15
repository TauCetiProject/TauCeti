/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization

import Mathlib.Analysis.Analytic.Polynomial
import TauCeti.Analysis.Calculus.ContDiffZPow
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# The line bundles `𝒪(k)` on projective space

For an integer `k`, the line bundle `𝒪(k)` on projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)` is glued
from the trivial lines over the standard affine opens `U_i = {[v] | v i ≠ 0}` along the transition
functions `[v] ↦ (v i / v j) ^ k` on `U_i ∩ U_j`. It is the Mathlib vector-bundle core
`Projectivization.twistCore k`, with model fibre `𝕜` and charts indexed by the homogeneous
coordinates; there is no separate line-bundle carrier. Its transitions are analytic on the
overlaps, so it is an analytic vector bundle (`Projectivization.isContMDiff_twistCore`); for
`𝕜 = ℂ` it is a holomorphic line bundle on `ℂℙⁿ`.

## Conventions

In the frame of the chart `i`, the coordinate of a section of `𝒪(k)` given by a homogeneous
function `F` of degree `k` is `F v / v i ^ k` at `[v]`. The coordinate change from the chart `i`
to the chart `j` is therefore multiplication by `(v i / v j) ^ k`
(`Projectivization.twistTransition`). For `k = -1` this is the tautological line bundle: a vector
`w` of the line `[v]` has coordinate `w i` in the frame of the chart `i`, and these coordinates
transform by `twistTransition (-1)` (`Projectivization.twistTransition_neg_one_mul`). The value of
a section `s` of the core at `x` is its coordinate in the frame of the preferred chart
`(twistCore k).indexAt x`, which is the chart used by `chartAt` for the manifold structure.

The transition functions of `𝒪(k + l)` and `𝒪(-k)` are the products and inverses of those of
`𝒪(k)` and `𝒪(l)` (`Projectivization.twistTransition_add` and
`Projectivization.twistTransition_neg`), and `𝒪(0)` has trivial transitions.

A homogeneous polynomial `P` of degree `d` defines the section `homogeneousSection P` of `𝒪(d)`,
whose coordinate in the chart `j` is its dehomogenization `dehomogenize j P` read in the affine
chart (`Projectivization.homogeneousSection_coord`). It is analytic
(`Projectivization.contMDiff_homogeneousSection`), and the assignment `P ↦ homogeneousSection P`
is injective on homogeneous polynomials of degree `d`
(`Projectivization.homogeneousSection_eq_zero_iff`).

## Main declarations

* `Projectivization.twistTransition k i j`: the transition function of `𝒪(k)`.
* `Projectivization.twistCore k`: the vector-bundle core of `𝒪(k)`.
* `Projectivization.isContMDiff_twistCore`: `𝒪(k)` is an analytic line bundle.
* `Projectivization.contMDiff_section_twistCore_iff`: a section of `𝒪(k)` is `C^r` exactly when
  its coordinate in every standard chart is `C^r` on that chart.
* `Projectivization.homogeneousSection`: the section of `𝒪(d)` defined by a homogeneous
  polynomial of degree `d`, analytic by `Projectivization.contMDiff_homogeneousSection`.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1 (line bundles
  `H` and their powers on projective space) and §2.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public noncomputable section

open Bundle Set MvPolynomial
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

/-! ### Transition functions -/

section Transition

variable {𝕜 ι : Type*} [Field 𝕜]

/-- The transition function of `𝒪(k)` from the chart `i` to the chart `j` of projective space:
`[v] ↦ (v i / v j) ^ k`, computed on the chosen representative
(`Projectivization.twistTransition_mk` for arbitrary homogeneous coordinates). -/
def twistTransition (k : ℤ) (i j : ι) (x : ℙ 𝕜 (ι → 𝕜)) : 𝕜 :=
  (x.rep i / x.rep j) ^ k

/-- The transition function of `𝒪(k)` on the chosen representative. -/
theorem twistTransition_def (k : ℤ) (i j : ι) (x : ℙ 𝕜 (ι → 𝕜)) :
    twistTransition k i j x = (x.rep i / x.rep j) ^ k :=
  (rfl)

/-- The transition function of `𝒪(k)` in arbitrary homogeneous coordinates. -/
@[simp]
theorem twistTransition_mk (k : ℤ) (i j : ι) (v : ι → 𝕜) (hv : v ≠ 0) :
    twistTransition k i j (mk 𝕜 v hv) = (v i / v j) ^ k := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep 𝕜 v hv
  simp only [twistTransition, ← ha, Pi.smul_apply, Units.smul_def, smul_eq_mul]
  rw [mul_div_mul_left _ _ a.ne_zero]

/-- On the chart `i`, the transition from a chart to itself is the identity. -/
@[simp]
theorem twistTransition_self (k : ℤ) {i : ι} {x : ℙ 𝕜 (ι → 𝕜)}
    (hx : x ∈ affineOpen i) : twistTransition k i i x = 1 := by
  simp [twistTransition, div_self ((mem_affineOpen_iff i x).1 hx)]

/-- `𝒪(0)` has trivial transition functions. -/
@[simp]
theorem twistTransition_zero (i j : ι) (x : ℙ 𝕜 (ι → 𝕜)) :
    twistTransition 0 i j x = 1 := by
  simp [twistTransition]

/-- The transition of `𝒪(-k)` is the inverse of the transition of `𝒪(k)`. -/
theorem twistTransition_neg (k : ℤ) (i j : ι) (x : ℙ 𝕜 (ι → 𝕜)) :
    twistTransition (-k) i j x = (twistTransition k i j x)⁻¹ := by
  simp [twistTransition, zpow_neg]

/-- The transition of `𝒪(k + l)` is the product of the transitions of `𝒪(k)` and `𝒪(l)` on the
overlap of the two charts. -/
theorem twistTransition_add (k l : ℤ) {i j : ι} {x : ℙ 𝕜 (ι → 𝕜)}
    (hi : x ∈ affineOpen i) (hj : x ∈ affineOpen j) :
    twistTransition (k + l) i j x = twistTransition k i j x * twistTransition l i j x :=
  zpow_add₀ (div_ne_zero ((mem_affineOpen_iff i x).1 hi) ((mem_affineOpen_iff j x).1 hj)) k l

/-- The transition functions of `𝒪(k)` satisfy the cocycle identity wherever the middle chart is
defined. -/
theorem twistTransition_mul_twistTransition (k : ℤ) (i : ι) {j : ι}
    (l : ι) {x : ℙ 𝕜 (ι → 𝕜)} (hj : x ∈ affineOpen j) :
    twistTransition k j l x * twistTransition k i j x = twistTransition k i l x := by
  have hj' := (mem_affineOpen_iff j x).1 hj
  simp only [twistTransition]
  rw [← mul_zpow, mul_comm, div_mul_div_cancel₀ hj']

/-- **`𝒪(-1)` is the tautological line bundle.** A vector `w` of the line `x` has coordinate
`w i` in the frame of the chart `i`, and these coordinates transform by the transition functions
of `𝒪(-1)`. -/
theorem twistTransition_neg_one_mul {i : ι} (j : ι)
    {x : ℙ 𝕜 (ι → 𝕜)} (hi : x ∈ affineOpen i) {w : ι → 𝕜}
    (hw : w ∈ x.submodule) : twistTransition (-1) i j x * w i = w j := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (by simpa [submodule_eq] using hw)
  have hi' := (mem_affineOpen_iff i x).1 hi
  simp only [twistTransition, zpow_neg, zpow_one, inv_div, Pi.smul_apply, smul_eq_mul]
  field_simp

end Transition

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- The transition functions of `𝒪(k)` are `C^r`, for every `r` including the analytic order
`ω`, on the overlaps of the standard charts. -/
theorem contMDiffOn_twistTransition (k : ℤ) (i j : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜) r (twistTransition k i j)
      (affineOpen (K := 𝕜) i ∩ affineOpen j) := by
  have hlin : ContDiff 𝕜 r fun z : Fin n → 𝕜 ↦ Fin.insertNth (α := fun _ ↦ 𝕜) j 1 z i :=
    (contDiff_apply 𝕜 (fun _ ↦ 𝕜) i).comp
      ((contDiff_const (c := (1 : 𝕜))).finInsertNth (F := fun _ ↦ 𝕜) j contDiff_id)
  have hratio : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜) r
      (fun x : ℙ 𝕜 (Fin (n + 1) → 𝕜) ↦ x.rep i / x.rep j) (affineOpen j) :=
    (hlin.contMDiff.comp_contMDiffOn (contMDiffOn_affineChart j r)).congr fun x hx ↦
      rep_div_rep_eq_insertNth_affineChart i hx
  intro x ⟨hi, hj⟩
  have h0 : x.rep i / x.rep j ≠ 0 :=
    div_ne_zero ((mem_affineOpen_iff i x).1 hi) ((mem_affineOpen_iff j x).1 hj)
  have hpow : ContMDiffAt 𝓘(𝕜) 𝓘(𝕜) r (fun u : 𝕜 ↦ u ^ k) (x.rep i / x.rep j) :=
    (contDiffAt_id.zpow (Or.inl h0)).contMDiffAt
  exact hpow.comp_contMDiffWithinAt x ((hratio x hj).mono inter_subset_right)

/-! ### The line bundle -/

/-- The line bundle `𝒪(k)` on projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, as a Mathlib
vector-bundle core with model fibre `𝕜`. The chart `i` is trivial over the standard affine open
`U_i`, the coordinate change from the chart `i` to the chart `j` is multiplication by
`twistTransition k i j`, and the preferred chart at `x` is the one used by `chartAt`. -/
def twistCore (k : ℤ) :
    VectorBundleCore 𝕜 (ℙ 𝕜 (Fin (n + 1) → 𝕜)) 𝕜 (Fin (n + 1)) where
  baseSet i := affineOpen i
  isOpen_baseSet i := isOpen_affineOpen i
  indexAt x := (exists_mem_affineOpen x).choose
  mem_baseSet_at x := (exists_mem_affineOpen x).choose_spec
  coordChange i j x := ContinuousLinearMap.lsmul 𝕜 𝕜 (twistTransition k i j x)
  coordChange_self i x hx v := by simp [twistTransition_self k hx]
  continuousOn_coordChange i j :=
    (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜 →L[𝕜] 𝕜).continuous.comp_continuousOn
      (contMDiffOn_twistTransition k i j 0).continuousOn
  coordChange_comp i j l x hx v := by
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, ← mul_assoc]
    rw [twistTransition_mul_twistTransition k i l hx.1.2]

/-- The chart `i` of `𝒪(k)` is defined over the standard affine open `U_i`. It is not a
simp lemma, since `VectorBundleCore.baseSet_at` already rewrites its left side into the left side
of `twistCore_localTriv_baseSet`. -/
theorem twistCore_baseSet (k : ℤ) (i : Fin (n + 1)) :
    (twistCore (𝕜 := 𝕜) k).baseSet i = affineOpen i :=
  (rfl)

/-- The chart `i` of `𝒪(k)` is trivial over the standard affine open `U_i`. -/
@[simp]
theorem twistCore_localTriv_baseSet (k : ℤ) (i : Fin (n + 1)) :
    ((twistCore (𝕜 := 𝕜) k).localTriv i).baseSet = affineOpen i :=
  (rfl)

/-- The preferred chart of `𝒪(k)` at `x` is the chart of the manifold structure at `x`. -/
theorem chartAt_eq_affineOpenPartialHomeomorph_twistCore_indexAt (k : ℤ)
    (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    chartAt (Fin n → 𝕜) x = affineOpenPartialHomeomorph ((twistCore k).indexAt x) :=
  (rfl)

@[simp]
theorem twistCore_coordChange_apply (k : ℤ) (i j : Fin (n + 1)) (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (v : 𝕜) : (twistCore k).coordChange i j x v = twistTransition k i j x * v :=
  (rfl)

/-- **`𝒪(k)` is an analytic line bundle.** Its transition functions are analytic, so for
`𝕜 = ℂ` it is a holomorphic line bundle on `ℂℙⁿ`. -/
instance isContMDiff_twistCore (k : ℤ) :
    (twistCore (𝕜 := 𝕜) (n := n) k).IsContMDiff 𝓘(𝕜, Fin n → 𝕜) ω where
  contMDiffOn_coordChange i j :=
    (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜 →L[𝕜] 𝕜).contMDiff.comp_contMDiffOn
      (contMDiffOn_twistTransition k i j ω)

/-! ### Sections -/

/-- In the frame of the chart `j`, a section `s` of `𝒪(k)` has the coordinate
`twistTransition k ((twistCore k).indexAt x) j x * s x` at `x`. -/
theorem twistCore_localTriv_apply (k : ℤ) (j : Fin (n + 1)) (s : ℙ 𝕜 (Fin (n + 1) → 𝕜) → 𝕜)
    (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    ((twistCore k).localTriv j ⟨x, s x⟩).2 =
      twistTransition k ((twistCore k).indexAt x) j x * s x :=
  (rfl)

/-- **Sections of `𝒪(k)` in the standard charts.** A section `s` of `𝒪(k)` is `C^r` exactly when,
for every `j`, its coordinate `x ↦ twistTransition k ((twistCore k).indexAt x) j x * s x` in the
frame of the chart `j` is `C^r` on the standard affine open `U_j`. -/
theorem contMDiff_section_twistCore_iff (k : ℤ) {r : ℕ∞ω} (s : ℙ 𝕜 (Fin (n + 1) → 𝕜) → 𝕜) :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) (𝓘(𝕜, Fin n → 𝕜).prod 𝓘(𝕜)) r
        (fun x ↦ TotalSpace.mk' 𝕜 (E := (twistCore k).Fiber) x (s x)) ↔
      ∀ j, ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜) r
        (fun x ↦ twistTransition k ((twistCore k).indexAt x) j x * s x) (affineOpen j) := by
  let s' : ∀ x, (twistCore (𝕜 := 𝕜) (n := n) k).Fiber x := s
  have key (j : Fin (n + 1)) := by
    haveI : MemTrivializationAtlas ((twistCore (𝕜 := 𝕜) (n := n) k).localTriv j) := ⟨⟨j, rfl⟩⟩
    exact ((twistCore (𝕜 := 𝕜) (n := n) k).localTriv j).contMDiffOn_section_iff
      (IB := 𝓘(𝕜, Fin n → 𝕜)) (n := r) (s := s') (a := affineOpen j) (isOpen_affineOpen j)
      fun _ hx ↦ hx
  rw [← contMDiffOn_univ, ← iUnion_affineOpen,
    contMDiffOn_iUnion_iff_of_isOpen fun j ↦ isOpen_affineOpen j]
  exact forall_congr' key

/-! ### Sections from homogeneous polynomials -/

/-- The section of `𝒪(d)` defined by a polynomial `P`, homogeneous of degree `d`: its coordinate in
the frame of the chart `i` at `[v]` is `P v / v i ^ d`. -/
def homogeneousSection (d : ℕ) (P : MvPolynomial (Fin (n + 1)) 𝕜)
    (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) : 𝕜 :=
  eval x.rep P / x.rep ((twistCore (𝕜 := 𝕜) (d : ℤ)).indexAt x) ^ d

/-- The section `homogeneousSection d P` on the chosen representative, in the frame of the
preferred chart. -/
theorem homogeneousSection_def (d : ℕ) (P : MvPolynomial (Fin (n + 1)) 𝕜)
    (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    homogeneousSection d P x =
      eval x.rep P / x.rep ((twistCore (𝕜 := 𝕜) (d : ℤ)).indexAt x) ^ d :=
  (rfl)

/-- The section defined by the zero polynomial is zero. -/
@[simp]
theorem homogeneousSection_zero (d : ℕ) :
    homogeneousSection (𝕜 := 𝕜) (n := n) d 0 = 0 := by
  funext x
  simp [homogeneousSection]

/-- The section defined by a sum of polynomials is the sum of their sections. -/
@[simp]
theorem homogeneousSection_add (d : ℕ) (P Q : MvPolynomial (Fin (n + 1)) 𝕜) :
    homogeneousSection d (P + Q) = homogeneousSection d P + homogeneousSection d Q := by
  funext x
  simp [homogeneousSection, add_div]

/-- The section defined by a scalar multiple of a polynomial is the scalar multiple of its
section. -/
@[simp]
theorem homogeneousSection_smul (d : ℕ) (c : 𝕜) (P : MvPolynomial (Fin (n + 1)) 𝕜) :
    homogeneousSection d (c • P) = c • homogeneousSection d P := by
  funext x
  simp [homogeneousSection, smul_eq_C_mul, mul_div_assoc]

/-- The coordinate of `homogeneousSection d P` in the frame of the chart `j` is
`P v / v j ^ d`, computed on the chosen representative `v` of `x`. -/
theorem twistTransition_mul_homogeneousSection (d : ℕ) (P : MvPolynomial (Fin (n + 1)) 𝕜)
    (j : Fin (n + 1)) (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    twistTransition (d : ℤ) ((twistCore (d : ℤ)).indexAt x) j x * homogeneousSection d P x =
      eval x.rep P / x.rep j ^ d := by
  have ha : x.rep ((twistCore (𝕜 := 𝕜) (d : ℤ)).indexAt x) ≠ 0 :=
    (mem_affineOpen_iff _ x).1 ((twistCore (𝕜 := 𝕜) (d : ℤ)).mem_baseSet_at x)
  simp only [homogeneousSection, twistTransition, zpow_natCast]
  rw [div_pow]
  field_simp

/-- On the chart `j`, the coordinate of `homogeneousSection d P` in the frame of the chart `j` is
the dehomogenization of `P` at the affine coordinates. -/
theorem homogeneousSection_coord {d : ℕ} {P : MvPolynomial (Fin (n + 1)) 𝕜}
    (hP : P.IsHomogeneous d) {j : Fin (n + 1)} {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)}
    (hj : x ∈ affineOpen j) :
    twistTransition (d : ℤ) ((twistCore (d : ℤ)).indexAt x) j x * homogeneousSection d P x =
      eval (affineChart j x) (TauCeti.dehomogenize j P) := by
  rw [twistTransition_mul_homogeneousSection]
  have hx : x = mk 𝕜 x.rep x.rep_ne_zero := (mk_rep x).symm
  conv_rhs => rw [hx, affineChart_mk]
  rw [TauCeti.eval_dehomogenize_div j hP _ ((mem_affineOpen_iff j x).1 hj), inv_pow,
    div_eq_inv_mul]

/-- **Homogeneous polynomials are global sections.** For `P` homogeneous of degree `d`, the
section `homogeneousSection d P` of `𝒪(d)` is `C^r` for every `r`, including the analytic order
`ω`; for `𝕜 = ℂ` it is a global holomorphic section. -/
theorem contMDiff_homogeneousSection {d : ℕ} {P : MvPolynomial (Fin (n + 1)) 𝕜}
    (hP : P.IsHomogeneous d) (r : ℕ∞ω) :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) (𝓘(𝕜, Fin n → 𝕜).prod 𝓘(𝕜)) r
      (fun x ↦ TotalSpace.mk' 𝕜 (E := (twistCore (𝕜 := 𝕜) (d : ℤ)).Fiber) x
        (homogeneousSection (𝕜 := 𝕜) d P x)) := by
  rw [contMDiff_section_twistCore_iff]
  intro j
  exact ((AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜))
    (TauCeti.dehomogenize j P)).contDiff.contMDiff.comp_contMDiffOn
    (contMDiffOn_affineChart j r)).congr fun x hx ↦ homogeneousSection_coord hP hx

/-- The section `homogeneousSection d P` vanishes at `[v]` exactly when `P` vanishes at `v`. -/
@[simp]
theorem homogeneousSection_mk_eq_zero_iff {d : ℕ} {P : MvPolynomial (Fin (n + 1)) 𝕜}
    (hP : P.IsHomogeneous d) (v : Fin (n + 1) → 𝕜) (hv : v ≠ 0) :
    homogeneousSection d P (mk 𝕜 v hv) = 0 ↔ eval v P = 0 := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep 𝕜 v hv
  have hi := (mem_affineOpen_iff _ _).1
    ((twistCore (𝕜 := 𝕜) (n := n) (d : ℤ)).mem_baseSet_at (mk 𝕜 v hv))
  have hrep : eval (mk 𝕜 v hv).rep P = (a : 𝕜) ^ d * eval v P := by
    rw [← ha, Units.smul_def, hP.eval_smul]
  simp [homogeneousSection, hrep, hi]

/-- **Distinct homogeneous polynomials give distinct sections.** A homogeneous polynomial of
degree `d` whose section of `𝒪(d)` vanishes identically is zero. -/
@[simp]
theorem homogeneousSection_eq_zero_iff {d : ℕ} {P : MvPolynomial (Fin (n + 1)) 𝕜}
    (hP : P.IsHomogeneous d) : homogeneousSection d P = 0 ↔ P = 0 := by
  refine ⟨fun h ↦ hP.eq_zero_of_forall_eval_eq_zero fun v ↦ ?_, fun h ↦ ?_⟩
  · have hz (w : Fin (n + 1) → 𝕜) (hw : w ≠ 0) : eval w P = 0 :=
      (homogeneousSection_mk_eq_zero_iff hP w hw).1 (congrFun h _)
    by_cases hv : v = 0
    · have hw : (Pi.single 0 1 : Fin (n + 1) → 𝕜) ≠ 0 := by simp
      rw [hv, ← zero_smul 𝕜 (Pi.single 0 1 : Fin (n + 1) → 𝕜),
        hP.eval_smul, hz _ hw, mul_zero]
    · exact hz v hv
  · funext x
    simp [homogeneousSection, h]

end Projectivization

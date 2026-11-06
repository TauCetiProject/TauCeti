/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.Duplication.Basic
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.Duplication.Domain
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.JointAnalytic
import TauCeti.Analysis.Complex.RealIdentity
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Carlson duplication on the complex slit plane

Carlson's duplication identity for `R_F` holds for slit-plane nodes with at most one zero.
The duplication parameter is the symmetric sum of products of principal square roots.
The transformed nodes are strictly in the slit plane, including when an input is zero.

The real duplication identity extends by the identity principle, one variable at a time.
Joint holomorphy of `R_F` justifies simultaneous variation of the three transformed nodes.
Keeping a possible zero node fixed during the first two continuations includes the boundary
case without a limiting argument at the branch point.

## References

* NIST DLMF §19.26(ii), especially 19.26.18.
* B. C. Carlson, *Computing elliptic integrals by duplication*, Numer. Math. 33 (1979), 1–16.

The variable-by-variable continuation strategy also appears in B. Braams' Apache-2.0
`lean-codes`, `Carlson/Elliptic/Addition.lean` at commit `2b8cba1`
(`dupDefect_extend` and `carlsonRF_duplication`). Here joint holomorphy is proved from the
direct integral rather than the general Carlson `R`-function, and the continuation includes
one zero node.
-/

public section

open Set

namespace Complex

private noncomputable def duplicationRHS (x y z : ℂ) : ℂ :=
  let l := sqrt x * sqrt y + sqrt y * sqrt z + sqrt z * sqrt x
  carlsonRF ((x + l) / 4) ((y + l) / 4) ((z + l) / 4)

private theorem duplicationRHS_comm_left (x y z : ℂ) :
    duplicationRHS x y z = duplicationRHS y x z := by
  have hl : sqrt x * sqrt y + sqrt y * sqrt z + sqrt z * sqrt x =
      sqrt y * sqrt x + sqrt x * sqrt z + sqrt z * sqrt y := by ring
  simp only [duplicationRHS, ← hl, carlsonRF_comm_left]

private theorem duplicationRHS_comm_right (x y z : ℂ) :
    duplicationRHS x y z = duplicationRHS x z y := by
  have hl : sqrt x * sqrt y + sqrt y * sqrt z + sqrt z * sqrt x =
      sqrt x * sqrt z + sqrt z * sqrt y + sqrt y * sqrt x := by ring
  simp only [duplicationRHS, ← hl, carlsonRF_comm_right]

private theorem analyticOnNhd_duplicationRHS_right {x y : ℂ}
    (hxy : x ∈ slitPlane ∨ y ∈ slitPlane) :
    AnalyticOnNhd ℂ (duplicationRHS x y) slitPlane := by
  intro z hz
  have hs : AnalyticAt ℂ sqrt z :=
    (differentiableOn_sqrt.analyticOnNhd isOpen_slitPlane) z hz
  have hl : AnalyticAt ℂ (fun w =>
      sqrt x * sqrt y + sqrt y * sqrt w + sqrt w * sqrt x) z := by
    fun_prop
  have hx' := carlson_duplication_node_mem_slitPlane x hxy (Or.inr hz)
  have hy' := carlson_duplication_node_mem_slitPlane y hxy.symm (Or.inr hz)
  have hz' := carlson_duplication_node_mem_slitPlane z (y := x) (z := y)
    (Or.inl hz) (Or.inl hz)
  rw [carlsonDuplicationLambda_comm_left y x z] at hy'
  rw [carlsonDuplicationLambda_comm_left z x y,
    carlsonDuplicationLambda_comm_right x z y] at hz'
  simp only [carlsonDuplicationLambda_def] at hx' hy' hz'
  exact ((analyticAt_const.add hl).div_const (c := 4)).carlsonRF
    ((analyticAt_const.add hl).div_const (c := 4))
    ((analyticAt_id.add hl).div_const (c := 4)) hx' hy' hz'

private theorem duplication_ofReal {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    carlsonRF x y z = duplicationRHS x y z := by
  have hs (t : ℝ) (ht : 0 ≤ t) : sqrt (t : ℂ) = (Real.sqrt t : ℂ) := by
    simpa using sqrt_of_nonneg (a := (t : ℂ)) (by exact_mod_cast ht)
  simpa only [duplicationRHS, hs x hx, hs y hy, hs z hz, ofReal_div, ofReal_add,
    ofReal_mul, ofReal_ofNat] using carlsonRF_ofReal_duplication hx hy hz

private theorem duplication_of_two_real {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y)
    {z : ℂ} (hz : z ∈ slitPlane) : carlsonRF x y z = duplicationRHS x y z := by
  have hy' : (y : ℂ) ∈ slitPlane := Or.inl hy
  exact AnalyticOnNhd.eqOn_slitPlane_of_ofReal_pos_eq
    (analyticOnNhd_carlsonRF_right (TauCeti.ofReal_mem_slitPlane_union_zero hx) hy')
    (analyticOnNhd_duplicationRHS_right (Or.inr hy'))
    (fun t ht => duplication_ofReal hx hy.le ht.le) hz

private theorem duplication_of_one_real {x : ℝ} (hx : 0 ≤ x)
    {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    carlsonRF x y z = duplicationRHS x y z := by
  have hrhs : AnalyticOnNhd ℂ (fun w => duplicationRHS x w z) slitPlane := by
    simpa only [duplicationRHS_comm_right (x : ℂ)] using
      analyticOnNhd_duplicationRHS_right (x := (x : ℂ)) (y := z) (Or.inr hz)
  exact AnalyticOnNhd.eqOn_slitPlane_of_ofReal_pos_eq
    (analyticOnNhd_carlsonRF_middle (TauCeti.ofReal_mem_slitPlane_union_zero hx) hz)
    hrhs (fun t ht => duplication_of_two_real hx ht hz) hy

private theorem duplication_of_mem_slitPlane {x y z : ℂ}
    (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    carlsonRF x y z = duplicationRHS x y z := by
  have hrhs : AnalyticOnNhd ℂ (fun w => duplicationRHS w y z) slitPlane := by
    have hfun : (fun w => duplicationRHS w y z) = duplicationRHS y z := by
      funext w
      rw [duplicationRHS_comm_left w, duplicationRHS_comm_right y]
    rw [hfun]
    exact analyticOnNhd_duplicationRHS_right (Or.inl hy)
  exact AnalyticOnNhd.eqOn_slitPlane_of_ofReal_pos_eq
    (analyticOnNhd_carlsonRF_left (Or.inl hy) hz)
    hrhs (fun t ht => duplication_of_one_real ht.le hy hz) hx

/-- **Carlson's duplication theorem** on the complex slit-plane domain (DLMF 19.26.18).
At most one input may be zero; every transformed node lies strictly in the slit plane. -/
theorem carlsonRF_duplication {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane ∪ {0})
    (hxy : x ≠ 0 ∨ y ≠ 0) (hxz : x ≠ 0 ∨ z ≠ 0) (hyz : y ≠ 0 ∨ z ≠ 0) :
    let l := sqrt x * sqrt y + sqrt y * sqrt z + sqrt z * sqrt x
    carlsonRF x y z = carlsonRF ((x + l) / 4) ((y + l) / 4) ((z + l) / 4) := by
  -- Use the local right-hand side so its permutation lemmas apply before unfolding it.
  suffices h : carlsonRF x y z = duplicationRHS x y z from h
  have hzero {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
      carlsonRF 0 y z = duplicationRHS 0 y z := by
    simpa using duplication_of_one_real (x := 0) le_rfl hy hz
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · rcases hz with hz | hz
      · exact duplication_of_mem_slitPlane hx hy hz
      · have hz0 : z = 0 := hz
        subst z
        simpa only [carlsonRF_comm_right x, carlsonRF_comm_left 0,
          duplicationRHS_comm_right x, duplicationRHS_comm_left 0] using hzero hx hy
    · have hy0 : y = 0 := hy
      subst y
      have hz' : z ∈ slitPlane := hz.resolve_right (by simpa using hyz)
      simpa only [carlsonRF_comm_left 0, duplicationRHS_comm_left 0] using hzero hx hz'
  · have hx0 : x = 0 := hx
    subst x
    exact hzero (hy.resolve_right (by simpa using hxy))
      (hz.resolve_right (by simpa using hxz))

end Complex

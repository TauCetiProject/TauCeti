/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Direction
public import TauCeti.LinearAlgebra.Dual.Basic

/-!
# Integral equations for rational-normal polyhedral directions

The direction of a nonempty rational-normal polyhedron of codimension `k` is
the common kernel of `k` independent real extensions of integral characters.
Offsets need not be rational: only the rows vanishing on the entire polyhedron
control its affine direction. This supplies integral conormals for actual cells,
including joints, rather than requiring a choice of defining equations as input.

## Attribution

Adapted from `Mei/Geometry/Convex/Polyhedron/Rational/Direction.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author: Codex; original copyright: Mei contributors.

-/

public section

open Set

namespace TauCeti.IsRationalNormalPolyhedron

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {P : Set V}

/-- A nonempty rational-normal polyhedron of codimension `k` has exactly `k`
independent integral conormals cutting out its affine direction. Arbitrary real
offsets, redundant inequalities, unboundedness and lineality are allowed. -/
theorem exists_direction_eq_iInf_ker (hP : IsRationalNormalPolyhedron h P)
    (hne : P.Nonempty) {k : ℕ}
    (hdim : Module.finrank ℝ (affineSpan ℝ P).direction + k = Module.finrank ℝ V) :
    ∃ m : Fin k → (N →+ ℤ),
      LinearIndependent ℝ (fun j => h.realCharacter (m j)) ∧
      (affineSpan ℝ P).direction =
        ⨅ j, (h.realCharacter (m j)).ker := by
  /- The proof uses `TauCeti.direction_affineSpan_setOf_forall_le` to identify the
  active equations, then Mathlib's `Submodule.exists_fun_fin_finrank_span_eq`
  and dual-coannihilator dimension formula to extract independent equations. -/
  classical
  let := h.finiteDimensional
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  have hcarrier : Q.carrier = {x | ∀ j, Q.inequality j x ≤ 0} :=
    Set.ext fun _ => RationalAffinePolyhedron.mem_carrier
  let I := {j : Fin Q.numConstraints // ∀ x ∈ Q.carrier, Q.inequality j x = 0}
  have hrows (j : I) := (Q.rational_linear j.val).exists_ker_eq_ker_realCharacter
  choose m hm using hrows
  let f : I → Module.Dual ℝ V := fun j => h.realCharacter (m j)
  have hdir : (affineSpan ℝ Q.carrier).direction = ⨅ j, (f j).ker := by
    simp_rw [f, ← hm]
    simpa only [I, iInf_subtype, hcarrier, Set.mem_ofPred_eq,
      ContinuousAffineMap.coe_toAffineMap] using
      TauCeti.direction_affineSpan_setOf_forall_le
        (fun j => (Q.inequality j).toAffineMap) (hcarrier ▸ hne)
  have hcoann : (Submodule.span ℝ (range f)).dualCoannihilator =
      (affineSpan ℝ Q.carrier).direction :=
    (Submodule.dualCoannihilator_span_range f).trans hdir.symm
  have hrank : Module.finrank ℝ (Submodule.span ℝ (range f)) = k := by
    have he := Subspace.finrank_add_finrank_dualCoannihilator_eq
      (Submodule.span ℝ (range f))
    rw [hcoann] at he
    omega
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℝ (range f)
  rw [hrank] at hex
  obtain ⟨b, hb, hspan, hlin⟩ := hex
  choose a ha using hb
  have heq : (fun j => h.realCharacter (m (a j))) = b := funext ha
  refine ⟨fun j => m (a j), heq.symm ▸ hlin, ?_⟩
  · rw [← hcoann, ← hspan, Submodule.dualCoannihilator_span_range, ← heq]

/-- A codimension-one rational-normal polyhedron has direction equal to the
kernel of a nonzero integral character. The affine offsets need not be rational. -/
theorem exists_direction_eq_ker (hP : IsRationalNormalPolyhedron h P)
    (hne : P.Nonempty)
    (hdim : Module.finrank ℝ (affineSpan ℝ P).direction + 1 = Module.finrank ℝ V) :
    ∃ m : N →+ ℤ, m ≠ 0 ∧ (affineSpan ℝ P).direction = (h.realCharacter m).ker := by
  obtain ⟨m, hlin, hdir⟩ := hP.exists_direction_eq_iInf_ker hne hdim
  refine ⟨m 0, ?_, ?_⟩
  · intro hm
    exact hlin.ne_zero 0 (by simp [hm])
  · simpa using hdir

/-- A codimension-two rational-normal polyhedron has tangent space cut out by
two integral characters with independent real extensions. The affine offsets
need not be rational. -/
theorem exists_direction_eq_inf_ker (hP : IsRationalNormalPolyhedron h P)
    (hne : P.Nonempty)
    (hdim : Module.finrank ℝ (affineSpan ℝ P).direction + 2 = Module.finrank ℝ V) :
    ∃ m n : N →+ ℤ, LinearIndependent ℝ ![h.realCharacter m, h.realCharacter n] ∧
      (affineSpan ℝ P).direction = (h.realCharacter m).ker ⊓ (h.realCharacter n).ker := by
  obtain ⟨m, hlin, hdir⟩ := hP.exists_direction_eq_iInf_ker hne hdim
  refine ⟨m 0, m 1, ?_, ?_⟩
  · convert hlin using 1
    ext j
    fin_cases j <;> simp
  · rw [hdir]
    ext v
    simp only [Submodule.mem_iInf, Submodule.mem_inf, LinearMap.mem_ker, Fin.forall_fin_two]

/-- A nonempty codimension-two rational-normal polyhedron and a transverse lattice
vector determine a nonzero integral normal to the swept direction. The affine
polyhedron need not contain a lattice point.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Joint.lean`, commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0; Mei contributors, author Codex). -/
theorem exists_swept_direction_normal (hP : IsRationalNormalPolyhedron h P)
    (hne : P.Nonempty)
    (hdim : Module.finrank ℝ (affineSpan ℝ P).direction + 2 = Module.finrank ℝ V)
    (v : N) (hv : i v ∉ (affineSpan ℝ P).direction) :
    ∃ m : N →+ ℤ, m ≠ 0 ∧
      (h.realCharacter m).ker = (affineSpan ℝ P).direction ⊔ ℝ ∙ i v := by
  obtain ⟨f, g, hind, hfg⟩ := hP.exists_direction_eq_inf_ker hne hdim
  have hv' := hfg ▸ hv
  refine ⟨f v • g - g v • f, ?_, ?_⟩
  · intro he
    apply LinearMap.apply_smul_sub_apply_smul_ne_zero (h.realCharacter f) (h.realCharacter g)
      hind hv'
    simpa only [map_sub, map_zsmul, map_zero, h.realCharacter_apply,
      ← Int.cast_smul_eq_zsmul ℝ] using congrArg h.realCharacter he
  · rw [h.ker_realCharacter_apply_smul_sub_apply_smul f g v hv', ← hfg]

end TauCeti.IsRationalNormalPolyhedron

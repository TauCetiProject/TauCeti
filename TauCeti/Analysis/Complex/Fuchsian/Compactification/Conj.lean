/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Manifold
public import TauCeti.Analysis.Complex.Fuchsian.Conj
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Conj
public import TauCeti.Geometry.Manifold.Complex.Chart
public import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Compactified quotients of conjugate Fuchsian groups

Let `Γ ≤ PSL(2, ℝ)` be discrete, `g ∈ PSL(2, ℝ)`, and let `Γ' = g Γ g⁻¹`, written
`ConjAct.toConjAct g • Γ = Γ'`. Translation by `g` induces a map
`Subgroup.compactifiedQuotientConj` of compactified quotients: on the coarse quotient it is the
homeomorphism `Subgroup.quotientConjHomeomorph` sending the orbit of `z` to the orbit of `g • z`,
and at the cusps it is the bijection `Subgroup.cuspOrbitConjEquiv` of cusp orbits.

This map is a biholomorphism, `Subgroup.CompactifiedQuotient.conjBiholomorph`, whose inverse is the
map induced by `g⁻¹`. Along the coarse quotient this is holomorphic descent. At a cusp, transport
the cusp datum `D` to the cusp datum `D.conj h` of `Γ'`: it maps the cusp neighbourhood of `D` at
height `A` into that of `D.conj h` at the same height, and the cusp charts of the two data agree
after the map (`Subgroup.CompactifiedQuotient.cuspChart_conj_compactifiedQuotientConj`), because
the q-coordinate of `D.conj h` at `g • z` is the q-coordinate of `D` at `z`. So, read in these
charts, the map is the identity of a disc. In particular conjugate Fuchsian groups have
biholomorphic compactified quotients, and every element of the normalizer of `Γ` acts on the
compactified quotient of `Γ` by biholomorphisms. The construction is functorial: `g = 1` gives the
identity (`Subgroup.CompactifiedQuotient.conjBiholomorph_one`), and conjugating by `g` and then by
`g'` is conjugating by `g' * g` (`Subgroup.CompactifiedQuotient.conjBiholomorph_trans`). Only `Γ`
is assumed discrete: discreteness of `Γ'` follows
(`TauCeti.discreteTopology_of_conjAct_smul_eq`).

## Main declarations

* `Subgroup.compactifiedQuotientConj`: the map of compactified quotients induced by conjugation,
  with the identity and composition laws `Subgroup.compactifiedQuotientConj_one` and
  `Subgroup.compactifiedQuotientConj_comp`.
* `Subgroup.CompactifiedQuotient.continuous_compactifiedQuotientConj` and
  `Subgroup.CompactifiedQuotient.mdifferentiable_compactifiedQuotientConj`: it is continuous and
  holomorphic.
* `Subgroup.CompactifiedQuotient.conjBiholomorph`: the biholomorphism of compactified quotients,
  with `Subgroup.CompactifiedQuotient.conjBiholomorph_symm`,
  `Subgroup.CompactifiedQuotient.conjBiholomorph_one` and
  `Subgroup.CompactifiedQuotient.conjBiholomorph_trans`.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, Chapter 4.
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.4–2.5.
-/

public noncomputable section

open Filter Function MulAction Set Topology TauCeti.Subgroup.CuspDatum UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups Pointwise

namespace Subgroup

variable {Γ Γ' : Subgroup PSL(2, ℝ)} {g : PSL(2, ℝ)}

/-- The map of compactified quotients induced by conjugation: if `Γ' = g Γ g⁻¹`, it sends the
orbit of `z` to the orbit of `g • z`, and the cusp orbit of `c` to the cusp orbit of `g • c`. -/
def compactifiedQuotientConj (h : ConjAct.toConjAct g • Γ = Γ') :
    Γ.CompactifiedQuotient → Γ'.CompactifiedQuotient
  | .ofQuotient p => .ofQuotient (quotientConjHomeomorph h p)
  | .ofCusp C => .ofCusp (cuspOrbitConjEquiv h C)

@[simp]
theorem compactifiedQuotientConj_ofQuotient (h : ConjAct.toConjAct g • Γ = Γ')
    (p : orbitRel.Quotient Γ ℍ) :
    compactifiedQuotientConj h (.ofQuotient p) = .ofQuotient (quotientConjHomeomorph h p) :=
  (rfl)

@[simp]
theorem compactifiedQuotientConj_ofCusp (h : ConjAct.toConjAct g • Γ = Γ') (C : Γ.CuspOrbit) :
    compactifiedQuotientConj h (.ofCusp C) = .ofCusp (cuspOrbitConjEquiv h C) :=
  (rfl)

/-- The map induced by `g⁻¹` is a left inverse of the map induced by `g`. -/
@[simp]
theorem compactifiedQuotientConj_compactifiedQuotientConj (h : ConjAct.toConjAct g • Γ = Γ')
    (x : Γ.CompactifiedQuotient) :
    compactifiedQuotientConj (by rw [← h, map_inv, inv_smul_smul] :
      ConjAct.toConjAct g⁻¹ • Γ' = Γ) (compactifiedQuotientConj h x) = x := by
  cases x with
  | ofQuotient p =>
    rw [compactifiedQuotientConj_ofQuotient, compactifiedQuotientConj_ofQuotient,
      ← quotientConjHomeomorph_symm h, Homeomorph.symm_apply_apply]
  | ofCusp C =>
    rw [compactifiedQuotientConj_ofCusp, compactifiedQuotientConj_ofCusp,
      ← cuspOrbitConjEquiv_symm h, Equiv.symm_apply_apply]

/-- Conjugation by `1` induces the identity of the compactified quotient. -/
@[simp]
theorem compactifiedQuotientConj_one (h : ConjAct.toConjAct (1 : PSL(2, ℝ)) • Γ = Γ) :
    compactifiedQuotientConj h = id := by
  funext x
  cases x <;> simp

/-- Conjugating by `g` and then by `g'` induces the same map of compactified quotients as
conjugating by `g' * g`. -/
@[simp]
theorem compactifiedQuotientConj_comp {Γ'' : Subgroup PSL(2, ℝ)} {g' : PSL(2, ℝ)}
    (h : ConjAct.toConjAct g • Γ = Γ') (h' : ConjAct.toConjAct g' • Γ' = Γ'') :
    compactifiedQuotientConj h' ∘ compactifiedQuotientConj h =
      compactifiedQuotientConj (by rw [map_mul, mul_smul, h, h'] :
        ConjAct.toConjAct (g' * g) • Γ = Γ'') := by
  funext x
  cases x with
  | ofQuotient p =>
      simp only [comp_apply, compactifiedQuotientConj_ofQuotient]
      rw [← Homeomorph.trans_apply, quotientConjHomeomorph_trans]
  | ofCusp C =>
      simp only [comp_apply, compactifiedQuotientConj_ofCusp]
      rw [← Equiv.trans_apply, cuspOrbitConjEquiv_trans]

namespace CompactifiedQuotient

/-- The map induced by conjugation sends the cusp neighbourhood of a cusp datum `D` at height `A`
into the cusp neighbourhood of the transported datum `D.conj h` at the same height. -/
theorem mapsTo_compactifiedQuotientConj_cuspNhd (h : ConjAct.toConjAct g • Γ = Γ')
    (D : Γ.CuspDatum) (A : ℝ) :
    MapsTo (compactifiedQuotientConj h) (cuspNhd D A) (cuspNhd (D.conj h) A) := by
  intro x hx
  cases x with
  | ofQuotient p =>
      obtain ⟨z, hz, rfl⟩ := (ofQuotient_mem_cuspNhd_iff D A).mp hx
      rw [compactifiedQuotientConj_ofQuotient, quotientConjHomeomorph_mk,
        ofQuotient_mem_cuspNhd_iff]
      exact ⟨g • z, (smul_mem_horodisc_conj_iff D h).mpr hz, rfl⟩
  | ofCusp C =>
      rw [(ofCusp_mem_cuspNhd_iff D A).mp hx, compactifiedQuotientConj_ofCusp,
        ← CuspDatum.cuspOrbit_conj]
      exact ofCusp_mem_cuspNhd _ A

variable [DiscreteTopology Γ]

/-- **The cusp charts are compatible with conjugation**: on the cusp neighbourhood of `D`, the cusp
chart of the transported datum `D.conj h` after the map induced by conjugation is the cusp chart of
`D`. -/
theorem cuspChart_conj_compactifiedQuotientConj (h : ConjAct.toConjAct g • Γ = Γ')
    (D : Γ.CuspDatum) {A : ℝ} (hA : D.width ≤ A) {x : Γ.CompactifiedQuotient}
    (hx : x ∈ cuspNhd D A) :
    letI := TauCeti.discreteTopology_of_conjAct_smul_eq h
    cuspChart (D.conj h) ((D.conj_width h).trans_le hA) (compactifiedQuotientConj h x) =
      cuspChart D hA x := by
  have := TauCeti.discreteTopology_of_conjAct_smul_eq h
  cases x with
  | ofQuotient p =>
      obtain ⟨z, hz, rfl⟩ := (ofQuotient_mem_cuspNhd_iff D A).mp hx
      rw [compactifiedQuotientConj_ofQuotient, quotientConjHomeomorph_mk,
        cuspChart_ofQuotient_mk _ _ ((smul_mem_horodisc_conj_iff D h).mpr hz),
        cuspChart_ofQuotient_mk D hA hz, coordinate_conj_smul]
  | ofCusp C =>
      rw [(ofCusp_mem_cuspNhd_iff D A).mp hx, compactifiedQuotientConj_ofCusp,
        ← CuspDatum.cuspOrbit_conj, cuspChart_ofCusp, cuspChart_ofCusp]

/-- The map of compactified quotients induced by conjugation is continuous, including at the
adjoined cusp points. -/
theorem continuous_compactifiedQuotientConj (h : ConjAct.toConjAct g • Γ = Γ') :
    letI := TauCeti.discreteTopology_of_conjAct_smul_eq h
    Continuous (compactifiedQuotientConj h) := by
  have := TauCeti.discreteTopology_of_conjAct_smul_eq h
  rw [continuous_iff_continuousAt]
  intro x
  cases x with
  | ofQuotient p =>
      have hcomp : ContinuousAt (compactifiedQuotientConj h ∘ ofQuotient) p :=
        (continuous_ofQuotient.comp (quotientConjHomeomorph h).continuous).continuousAt
      exact isOpenEmbedding_ofQuotient.continuousAt_iff.mp hcomp
  | ofCusp C =>
      obtain ⟨D, rfl⟩ := CuspDatum.cuspOrbit_surjective C
      rw [ContinuousAt, compactifiedQuotientConj_ofCusp, ← CuspDatum.cuspOrbit_conj D h]
      exact (nhds_basis_cuspNhd (D.conj h) 0).tendsto_right_iff.mpr fun A _ ↦
        mem_of_superset (cuspNhd_mem_nhds D A) (mapsTo_compactifiedQuotientConj_cuspNhd h D A)

/-- **The map of compactified quotients induced by conjugation is holomorphic.** Along the coarse
quotient this is holomorphic descent; at a cusp, read in the cusp charts of a cusp datum and of
its transport, the map is the identity. -/
theorem mdifferentiable_compactifiedQuotientConj (h : ConjAct.toConjAct g • Γ = Γ') :
    letI := TauCeti.discreteTopology_of_conjAct_smul_eq h
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (compactifiedQuotientConj h) := by
  have := TauCeti.discreteTopology_of_conjAct_smul_eq h
  intro x
  cases x with
  | ofQuotient p =>
      exact mdifferentiableAt_comp_ofQuotient_iff.mp
        ((mdifferentiable_ofQuotient _).comp p (mdifferentiable_quotientConjHomeomorph h p))
  | ofCusp C =>
      obtain ⟨D, rfl⟩ := CuspDatum.cuspOrbit_surjective C
      let e := cuspChart D le_rfl
      let e' := cuspChart (D.conj h) (D.conj_width h).le
      have he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 Γ.CompactifiedQuotient :=
        IsManifold.subset_maximalAtlas (cuspChart_mem_atlas D le_rfl)
      have he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 Γ'.CompactifiedQuotient :=
        IsManifold.subset_maximalAtlas (cuspChart_mem_atlas (D.conj h) (D.conj_width h).le)
      have hxe : ofCusp D.cuspOrbit ∈ e.source := ofCusp_mem_cuspChart_source D le_rfl
      have hfxe : compactifiedQuotientConj h (ofCusp D.cuspOrbit) ∈ e'.source := by
        simp [e']
      rw [← mdifferentiableWithinAt_univ,
        mdifferentiableWithinAt_iff_of_mem_maximalAtlas he he' hxe hfxe]
      refine ⟨(continuous_compactifiedQuotientConj h).continuousAt.continuousWithinAt, ?_⟩
      simp only [mfld_simps]
      rw [differentiableWithinAt_univ]
      -- In the two cusp charts the map is the identity near `0`.
      refine differentiableAt_id.congr_of_eventuallyEq ?_
      filter_upwards [e.open_target.mem_nhds (e.map_source hxe)] with q hq
      simp only [comp_apply, id]
      rw [cuspChart_conj_compactifiedQuotientConj h D le_rfl (by simpa [e] using e.map_target hq),
        e.right_inv hq]

/-- **Conjugate Fuchsian groups have biholomorphic compactified quotients.** If `Γ' = g Γ g⁻¹` for
a discrete `Γ`, translation by `g` induces a biholomorphism between the compactified quotients of
`Γ` and `Γ'`, sending the orbit of `z` to the orbit of `g • z` and the cusp orbit of `c` to the
cusp orbit of `g • c`. -/
def conjBiholomorph (h : ConjAct.toConjAct g • Γ = Γ') :
    letI := TauCeti.discreteTopology_of_conjAct_smul_eq h
    Γ.CompactifiedQuotient ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ Γ'.CompactifiedQuotient :=
  have := TauCeti.discreteTopology_of_conjAct_smul_eq h
  have h' : ConjAct.toConjAct g⁻¹ • Γ' = Γ := by rw [← h, map_inv, inv_smul_smul]
  { toFun := compactifiedQuotientConj h
    invFun := compactifiedQuotientConj h'
    left_inv := compactifiedQuotientConj_compactifiedQuotientConj h
    right_inv x := by
      cases x with
      | ofQuotient p =>
        rw [compactifiedQuotientConj_ofQuotient, compactifiedQuotientConj_ofQuotient,
          ← quotientConjHomeomorph_symm h, Homeomorph.apply_symm_apply]
      | ofCusp C =>
        rw [compactifiedQuotientConj_ofCusp, compactifiedQuotientConj_ofCusp,
          ← cuspOrbitConjEquiv_symm h, Equiv.apply_symm_apply]
    contMDiff_toFun := (mdifferentiable_compactifiedQuotientConj h).contMDiff
    contMDiff_invFun := (mdifferentiable_compactifiedQuotientConj h').contMDiff }

@[simp]
theorem coe_conjBiholomorph (h : ConjAct.toConjAct g • Γ = Γ') :
    letI := TauCeti.discreteTopology_of_conjAct_smul_eq h
    ⇑(conjBiholomorph h) = compactifiedQuotientConj h :=
  (rfl)

/-- The inverse of the biholomorphism induced by `g` is the one induced by `g⁻¹`. -/
@[simp]
theorem conjBiholomorph_symm (h : ConjAct.toConjAct g • Γ = Γ') :
    letI := TauCeti.discreteTopology_of_conjAct_smul_eq h
    (conjBiholomorph h).symm =
      conjBiholomorph (by rw [← h, map_inv, inv_smul_smul] : ConjAct.toConjAct g⁻¹ • Γ' = Γ) := by
  have := TauCeti.discreteTopology_of_conjAct_smul_eq h
  exact Diffeomorph.ext fun _ ↦ rfl

/-- Conjugation by `1` induces the identity biholomorphism. -/
@[simp]
theorem conjBiholomorph_one (h : ConjAct.toConjAct (1 : PSL(2, ℝ)) • Γ = Γ) :
    conjBiholomorph h = Diffeomorph.refl _ _ _ :=
  Diffeomorph.ext fun x ↦ congrFun (compactifiedQuotientConj_one h) x

/-- Conjugating by `g` and then by `g'` induces the same biholomorphism as conjugating by
`g' * g`. -/
@[simp]
theorem conjBiholomorph_trans {Γ'' : Subgroup PSL(2, ℝ)} {g' : PSL(2, ℝ)}
    (h : ConjAct.toConjAct g • Γ = Γ') (h' : ConjAct.toConjAct g' • Γ' = Γ'') :
    letI := TauCeti.discreteTopology_of_conjAct_smul_eq h
    letI := TauCeti.discreteTopology_of_conjAct_smul_eq h'
    (conjBiholomorph h).trans (conjBiholomorph h') =
      conjBiholomorph (by rw [map_mul, mul_smul, h, h'] :
        ConjAct.toConjAct (g' * g) • Γ = Γ'') := by
  have := TauCeti.discreteTopology_of_conjAct_smul_eq h
  have := TauCeti.discreteTopology_of_conjAct_smul_eq h'
  exact Diffeomorph.ext fun x ↦ congrFun (compactifiedQuotientConj_comp h h') x

end CompactifiedQuotient

end Subgroup

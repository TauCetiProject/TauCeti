/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup.SpecialUnitary
public import TauCeti.Topology.Algebra.ProperAction.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The twisted `SU(r)` representation model of surface moduli

Fix a rank `r : ℕ`, a complex scalar `ζ : ℂ`, and a genus `g : ℕ`. The **twisted relation set**
`TauCeti.GaugeModuli.relationSet r ζ g` consists of the tuples `(A₁, B₁, …, A_g, B_g)` in
`SU(r)` satisfying the punctured-surface relation

`⁅A₁, B₁⁆ ⋯ ⁅A_g, B_g⁆ = ζ • 1`,

where `⁅A, B⁆ = A * B * A⁻¹ * B⁻¹` is the group commutator. When `ζ = exp(2πi d / r)` is a
primitive `r`-th root of unity (corresponding to `gcd(r, d) = 1`), the quotient
`TauCeti.GaugeModuli.relationModuli r ζ g` of `relationSet r ζ g` by simultaneous conjugation is
the representation model of the fixed-determinant coprime `U(r)` moduli space of central-curvature
connections on a closed oriented surface of genus `g` (Wehrheim–Woodward, *Floer field theory for
coprime rank and degree*, §3).

## Main definitions

* `TauCeti.GaugeModuli.relationSet`: the level set `{x | ∏_j ⁅(x j).1, (x j).2⁆ = ζ • 1}` of
  `g`-tuples of pairs in `SU(r)`.
* `TauCeti.GaugeModuli.relationModuli`: the orbit quotient of `relationSet r ζ g` by simultaneous
  `SU(r)`-conjugation, with the quotient topology.
* `TauCeti.GaugeModuli.relationModuliEquivPSUOrbitQuotient`: homeomorphism identifying
  `relationModuli r ζ g` with the orbit space of the effective group
  `PSU(r) = (Matrix.specialUnitaryGroup.toPSL).range`.

## Main results

* `TauCeti.GaugeModuli.isClosed_relationSet`, `TauCeti.GaugeModuli.isCompact_relationSet`, and
  `T2Space (relationModuli r ζ g)`: the relation set is compact, the effective `PSU(r)` action is
  continuous and proper, and the quotient `relationModuli r ζ g` is compact Hausdorff.
* `TauCeti.GaugeModuli.eq_bot_or_eq_top_of_invariant_relationSet`: when `ζ` is a primitive `r`-th
  root of unity, every solution in `relationSet r ζ g` acts irreducibly on `ℂ^r`.
* `TauCeti.GaugeModuli.exists_eq_smul_one_of_commute_relationSet` and
  `TauCeti.GaugeModuli.eq_zero_of_commute_relationSet_of_trace_eq_zero`: Schur's lemma and
  vanishing of the trace-free commuting matrices (the infinitesimal stabilizer) at every solution.
* `TauCeti.GaugeModuli.relationSet_stabilizer_central`,
  `TauCeti.GaugeModuli.conjAct_smul_relationSet_eq_self_iff`,
  `TauCeti.GaugeModuli.psu_smul_relationSet_eq_self_iff`, and
  `TauCeti.GaugeModuli.stabilizer_psu_relationSet_eq_bot`: commuting elements of `SU(r)` are
  central (`relationSet_stabilizer_central`), every `SU(r)`-stabilizer equals the center `μ_r`
  (`conjAct_smul_relationSet_eq_self_iff`), and the effective `PSU(r)` action on
  `relationSet r ζ g` is free (`psu_smul_relationSet_eq_self_iff`,
  `stabilizer_psu_relationSet_eq_bot`).
* `TauCeti.GaugeModuli.isEmpty_relationModuli_zero`: the genus-zero moduli is empty for `r ≥ 2`
  and primitive `ζ`.
* `TauCeti.GaugeModuli.relationModuli_rank_one` and
  `TauCeti.GaugeModuli.simplyConnectedSpace_relationModuli_rank_one`: for `r = 1` and `ζ = 1`, the
  moduli is a point (hence simply connected) in every genus.
* Continuous central-twist action of `(Z(SU(r)) × Z(SU(r)))^g` (representing `H¹(X; μ_r)`) on both
  `relationSet r ζ g` and `relationModuli r ζ g`.

## References

* Katrin Wehrheim and Chris T. Woodward, *Floer field theory for coprime rank and degree*,
  arXiv:1601.04924, §3 (Theorem 3.3.3 and Remark 3.3.7).
* Aliakbar Daemi, Kenji Fukaya, and Maksim Lipyanskiy, *Lagrangians, SO(3)-instantons and the
  Atiyah–Floer conjecture*, arXiv:2109.07032, Remark 2.2 and Lemma 2.43.
-/

public section

open Matrix Matrix.specialUnitaryGroup
open scoped commutatorElement

namespace TauCeti

namespace GaugeModuli

section Definitions

/-- The twisted relation set: tuples `(A₁, B₁, …, A_g, B_g)` in `SU(r)` whose ordered product of
commutators `⁅A₁, B₁⁆ ⋯ ⁅A_g, B_g⁆` equals the scalar matrix `ζ • 1`. -/
def relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    Set (Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) :=
  {x | ((List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ) = ζ • 1}

@[simp]
theorem mem_relationSet_iff {r : ℕ} {ζ : ℂ} {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ} :
    x ∈ relationSet r ζ g ↔
      ((List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 :=
  Iff.rfl

theorem mem_relationSet_zero_iff {r : ℕ} {ζ : ℂ}
    {x : Fin 0 → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ} :
    x ∈ relationSet r ζ 0 ↔ (1 : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
  simp [relationSet]

theorem mem_relationSet_one_iff {r : ℕ} {ζ : ℂ}
    {x : Fin 1 → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ} :
    x ∈ relationSet r ζ 1 ↔
      ((⁅(x 0).1, (x 0).2⁆ : Matrix.specialUnitaryGroup (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
  simp [relationSet]

/-- Simultaneous conjugation in `SU(r)` preserves the twisted relation set. -/
theorem conjAct_smul_mem_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) : u • x ∈ relationSet r ζ g := by
  rw [mem_relationSet_iff] at hx ⊢
  set g₀ := ConjAct.ofConjAct u
  have hprod :
      (List.ofFn fun j => ⁅((u • x) j).1, ((u • x) j).2⁆).prod =
        g₀ * (List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod * g₀⁻¹ := by
    have hmap := map_list_prod (MulAut.conj g₀) (List.ofFn fun j => ⁅(x j).1, (x j).2⁆)
    rw [List.map_ofFn] at hmap
    simpa [Function.comp_def, MulAut.conj_apply, map_commutatorElement, ConjAct.smul_def, g₀] using
      hmap.symm
  rw [hprod]
  have hval : ((g₀ * (List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod * g₀⁻¹ :
      Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (g₀ : Matrix (Fin r) (Fin r) ℂ) * (ζ • (1 : Matrix (Fin r) (Fin r) ℂ)) *
        ((g₀⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
    simp [hx]
  rw [hval, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hmul : (g₀ : Matrix (Fin r) (Fin r) ℂ) *
      ((g₀⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = 1 :=
    congrArg Subtype.val (mul_inv_cancel g₀)
  rw [hmul]

/-- Simultaneous conjugation of `SU(r)` restricts to `relationSet r ζ g`. -/
instance instMulActionConjActRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  smul u x := ⟨u • x.val, conjAct_smul_mem_relationSet u x.property⟩
  one_smul x := Subtype.ext (one_smul _ x.val)
  mul_smul u v x := Subtype.ext (mul_smul u v x.val)

@[simp]
theorem coe_conjAct_smul_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (x : relationSet r ζ g) :
    ((u • x : relationSet r ζ g) :
      Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =
      u • x.val :=
  (rfl)

/-- The representation model `R_g / SU(r)` of the fixed-determinant surface moduli: the orbit
quotient of `relationSet r ζ g` by simultaneous `SU(r)`-conjugation, with the quotient topology. -/
abbrev relationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) : Type :=
  MulAction.orbitRel.Quotient (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g)

end Definitions

section ActionsAndTopology

instance instContinuousConstSMulConjActRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousConstSMul (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  continuous_const_smul u :=
    continuous_induced_rng.mpr <|
      (continuous_const_smul u).comp continuous_subtypeVal

/-- Two elements of `relationSet r ζ g` have the same class in `relationModuli r ζ g` if and only
if they are simultaneously conjugate by some `u ∈ SU(r)`. -/
theorem quotient_mk_relationModuli_eq_iff {r : ℕ} {ζ : ℂ} {g : ℕ} (x y : relationSet r ζ g) :
    (Quotient.mk _ x : relationModuli r ζ g) = Quotient.mk _ y ↔
      ∃ u : Matrix.specialUnitaryGroup (Fin r) ℂ, ConjAct.toConjAct u • x.val = y.val := by
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨(ConjAct.ofConjAct u)⁻¹, ?_⟩
    have hinv : u⁻¹ • x.val = y.val := by
      rw [← congrArg Subtype.val hu, coe_conjAct_smul_relationSet, inv_smul_smul]
    simpa [map_inv] using hinv
  · rintro ⟨u, hu⟩
    refine ⟨ConjAct.toConjAct u⁻¹, Subtype.ext ?_⟩
    simp [← hu, map_inv]

/-- The twisted relation set is closed in `(SU(r) × SU(r))^g`. -/
theorem isClosed_relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) : IsClosed (relationSet r ζ g) := by
  have hcont : Continuous fun x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ ×
      Matrix.specialUnitaryGroup (Fin r) ℂ =>
      ((List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ) := by
    refine continuous_subtypeVal.comp ?_
    simp_rw [List.ofFn_eq_map]
    refine continuous_list_prod (List.finRange g) fun j _ => ?_
    have hA : Continuous fun x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ ×
        Matrix.specialUnitaryGroup (Fin r) ℂ => (x j).1 :=
      continuous_fst.comp (continuous_apply j)
    have hB : Continuous fun x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ ×
        Matrix.specialUnitaryGroup (Fin r) ℂ => (x j).2 :=
      continuous_snd.comp (continuous_apply j)
    exact ((hA.mul hB).mul hA.inv).mul hB.inv
  exact isClosed_singleton.preimage hcont

/-- The twisted relation set is compact. -/
theorem isCompact_relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) : IsCompact (relationSet r ζ g) :=
  (isClosed_relationSet r ζ g).isCompact

instance instCompactSpaceRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    CompactSpace (relationSet r ζ g) :=
  isCompact_iff_compactSpace.mp (isCompact_relationSet r ζ g)

/-- Central elements of `SU(r)` act trivially on `relationSet r ζ g`. -/
theorem conjAct_smul_eq_self_of_mem_center {r : ℕ} {ζ : ℂ} {g : ℕ}
    {u : Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hu : u ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (x : relationSet r ζ g) : ConjAct.toConjAct u • x = x := by
  have hfix (a : Matrix.specialUnitaryGroup (Fin r) ℂ) : ConjAct.toConjAct u • a = a := by
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hu a).symm
  exact Subtype.ext <| funext fun j => Prod.ext (hfix (x.val j).1) (hfix (x.val j).2)

/-- The effective simultaneous conjugation action of `PSU(r)` on `relationSet r ζ g`. -/
noncomputable instance instMulActionPSURelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range (relationSet r ζ g) :=
  MulAction.compHom (relationSet r ζ g) <|
    (QuotientGroup.lift (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
        ProjectiveSpecialLinearGroup (Fin r) ℂ).ker
      ((MulAction.toPermHom (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
          (relationSet r ζ g)).comp ConjAct.toConjAct.toMonoidHom)
      (IsConcreteLE.le_iff.mpr fun _ hu => MonoidHom.mem_ker.mpr <| Equiv.ext fun x =>
        conjAct_smul_eq_self_of_mem_center (ker_toPSL_le_center hu) x)).comp
      (QuotientGroup.quotientKerEquivRange toPSL).symm.toMonoidHom

/-- On an element `toPSL.rangeRestrict u ∈ PSU(r)`, the `PSU(r)` action on `relationSet r ζ g`
agrees with simultaneous conjugation by `u ∈ SU(r)`. -/
@[simp]
theorem toPSL_rangeRestrict_smul_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : Matrix.specialUnitaryGroup (Fin r) ℂ) (x : relationSet r ζ g) :
    (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).rangeRestrict u • x =
      ConjAct.toConjAct u • x := by
  have hsymm : (QuotientGroup.quotientKerEquivRange
      (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
        ProjectiveSpecialLinearGroup (Fin r) ℂ)).symm (toPSL.rangeRestrict u) =
      QuotientGroup.mk u := by
    rw [MulEquiv.symm_apply_eq]
    simp only [QuotientGroup.quotientKerEquivRange, MulEquiv.ofBijective_apply,
      QuotientGroup.rangeKerLift]
    exact (QuotientGroup.lift_mk' (N := toPSL.ker) (φ := toPSL.rangeRestrict) _ u).symm
  rw [MulAction.compHom_smul_def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hsymm,
    QuotientGroup.lift_mk', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAction.toPermHom_apply, Equiv.Perm.smul_def, MulAction.toPerm_apply]

/-- The simultaneous conjugation map `SU(r) × relationSet r ζ g → relationSet r ζ g` is
continuous. -/
private theorem continuous_conjAct_smul_relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    Continuous fun p : Matrix.specialUnitaryGroup (Fin r) ℂ × relationSet r ζ g =>
      ConjAct.toConjAct p.1 • p.2 := by
  have hcoord (j : Fin g)
      (π : Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ →
        Matrix.specialUnitaryGroup (Fin r) ℂ) (hπ : Continuous π) :
      Continuous fun p : Matrix.specialUnitaryGroup (Fin r) ℂ × relationSet r ζ g =>
        p.1 * π (p.2.val j) * p.1⁻¹ :=
    (continuous_fst.mul
      (hπ.comp ((continuous_apply j).comp (continuous_subtypeVal.comp continuous_snd)))).mul
      continuous_fst.inv
  exact continuous_induced_rng.mpr (continuous_pi fun j =>
    (hcoord j Prod.fst continuous_fst).prodMk (hcoord j Prod.snd continuous_snd))

instance instContinuousSMulPSURelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousSMul (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range (relationSet r ζ g) where
  continuous_smul := by
    have hq : IsOpenQuotientMap
        ((toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
          ProjectiveSpecialLinearGroup (Fin r) ℂ).rangeRestrict :
          Matrix.specialUnitaryGroup (Fin r) ℂ → _) := by
      have heq : ((toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
            ProjectiveSpecialLinearGroup (Fin r) ℂ).rangeRestrict :
            Matrix.specialUnitaryGroup (Fin r) ℂ → _) =
          fun u => quotientKerToPSLContinuousMulEquiv (QuotientGroup.mk u) := by
        ext1 u
        exact Subtype.ext (coe_quotientKerToPSLContinuousMulEquiv_mk u).symm
      rw [heq]
      exact quotientKerToPSLContinuousMulEquiv.toHomeomorph.isOpenQuotientMap.comp
        QuotientGroup.isOpenQuotientMap_mk
    rw [← (hq.prodMap IsOpenQuotientMap.id).continuous_comp_iff]
    exact (continuous_conjAct_smul_relationSet r ζ g).congr fun ⟨u, x⟩ =>
      (toPSL_rangeRestrict_smul_relationSet u x).symm

/-- The effective `PSU(r)` action on `relationSet r ζ g` is proper, since `PSU(r)` is compact
and `relationSet r ζ g` is Hausdorff. -/
instance instProperSMulPSURelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ProperSMul (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range (relationSet r ζ g) := by
  have : CompactSpace (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range :=
    isCompact_iff_compactSpace.mp isCompact_range_toPSL
  exact TauCeti.properSMul_of_compactSpace _ _

/-- The moduli space `relationModuli r ζ g` is homeomorphic to the orbit space of the effective
`PSU(r)` action on `relationSet r ζ g`. -/
noncomputable def relationModuliEquivPSUOrbitQuotient (r : ℕ) (ζ : ℂ) (g : ℕ) :
    relationModuli r ζ g ≃ₜ
      MulAction.orbitRel.Quotient (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
        ProjectiveSpecialLinearGroup (Fin r) ℂ).range (relationSet r ζ g) where
  toFun := Quotient.map' id fun x y ⟨u, hu⟩ =>
    ⟨toPSL.rangeRestrict (ConjAct.ofConjAct u), by
      dsimp only [id_eq]
      rw [toPSL_rangeRestrict_smul_relationSet]
      simpa using hu⟩
  invFun := Quotient.map' id fun x y ⟨p, hp⟩ => by
    obtain ⟨u, rfl⟩ := toPSL.rangeRestrict_surjective p
    dsimp only [id_eq] at hp
    rw [toPSL_rangeRestrict_smul_relationSet] at hp
    exact ⟨ConjAct.toConjAct u, hp⟩
  left_inv q := Quotient.inductionOn q fun _ => rfl
  right_inv q := Quotient.inductionOn q fun _ => rfl
  continuous_toFun := continuous_quot_lift _ continuous_quot_mk
  continuous_invFun := continuous_quot_lift _ continuous_quot_mk

@[simp]
theorem relationModuliEquivPSUOrbitQuotient_mk {r : ℕ} {ζ : ℂ} {g : ℕ} (x : relationSet r ζ g) :
    relationModuliEquivPSUOrbitQuotient r ζ g (Quotient.mk _ x) = Quotient.mk'' x :=
  (rfl)

@[simp]
theorem relationModuliEquivPSUOrbitQuotient_symm_mk {r : ℕ} {ζ : ℂ} {g : ℕ}
    (x : relationSet r ζ g) :
    (relationModuliEquivPSUOrbitQuotient r ζ g).symm (Quotient.mk'' x) = Quotient.mk _ x :=
  (rfl)

/-- The representation model `relationModuli r ζ g` is Hausdorff, as the orbit space of the proper
`PSU(r)` action on `relationSet r ζ g`. -/
instance instT2SpaceRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) : T2Space (relationModuli r ζ g) :=
  (relationModuliEquivPSUOrbitQuotient r ζ g).isEmbedding.t2Space

end ActionsAndTopology

section IrreducibilityAndStabilizers

/-- The subgroup of `SU(r)` consisting of matrices preserving a complex subspace `V ≤ ℂ^r`. -/
private def invariantSubmoduleSubgroup {r : ℕ} (V : Submodule ℂ (Fin r → ℂ)) :
    Subgroup (Matrix.specialUnitaryGroup (Fin r) ℂ) where
  carrier := {A | ∀ v ∈ V, Matrix.toLin' (A : Matrix (Fin r) (Fin r) ℂ) v ∈ V}
  one_mem' := fun v hv => by simpa using hv
  mul_mem' := fun ha hb v hv => by
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using ha _ (hb v hv)
  inv_mem' := fun {A} hA => by
    have hmul : ((A⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
        (A : Matrix (Fin r) (Fin r) ℂ) = 1 := congrArg Subtype.val (inv_mul_cancel A)
    have hinj : Function.Injective (LinearMap.restrict
        (Matrix.toLin' (A : Matrix (Fin r) (Fin r) ℂ)) hA) := fun v w hvw => by
      apply Subtype.ext
      have hEq := congrArg (((A⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ) *ᵥ ·) (congrArg Subtype.val hvw)
      simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hmul] using hEq
    intro v hv
    obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨v, hv⟩
    have hAw : (A : Matrix (Fin r) (Fin r) ℂ) *ᵥ w = v := congrArg Subtype.val hw
    have hinvv : ((A⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ
        v = w := by
      rw [← hAw, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    simp [Matrix.toLin'_apply, hinvv]

/-- The restricted determinant homomorphism on the stabilizer subgroup of `V ≤ ℂ^r` in `SU(r)`. -/
private noncomputable def restrictDet {r : ℕ} (V : Submodule ℂ (Fin r → ℂ)) :
    invariantSubmoduleSubgroup V →* ℂ where
  toFun A := LinearMap.det (LinearMap.restrict
    (Matrix.toLin' (A.val : Matrix (Fin r) (Fin r) ℂ)) (fun v hv => A.property v hv))
  map_one' := by
    convert LinearMap.det_id
    exact LinearMap.ext fun ⟨v, hv⟩ => Subtype.ext (by simp)
  map_mul' A B := by
    rw [← LinearMap.det_comp]
    congr 1
    exact LinearMap.ext fun ⟨v, hv⟩ => Subtype.ext (by
      simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec])

/-- The restricted determinant homomorphism evaluates to `1` on group commutators. -/
private theorem restrictDet_commutatorElement {r : ℕ} (V : Submodule ℂ (Fin r → ℂ))
    (A B : invariantSubmoduleSubgroup V) : restrictDet V ⁅A, B⁆ = 1 := by
  rw [← MonoidHom.coe_toHomUnits (restrictDet V), map_commutatorElement,
    (Commute.all _ _).commutator_eq, Units.val_one]

/-- **Irreducibility of coprime twisted representations.** For a primitive `r`-th root of unity
`ζ`, no proper nontrivial subspace of `ℂ^r` is invariant under all entries `(x j).1` and
`(x j).2` of a solution `x ∈ relationSet r ζ g`. -/
theorem eq_bot_or_eq_top_of_invariant_relationSet {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) (V : Submodule ℂ (Fin r → ℂ))
    (hV : ∀ j, (∀ v ∈ V, Matrix.toLin' ((x j).1 : Matrix (Fin r) (Fin r) ℂ) v ∈ V) ∧
      (∀ v ∈ V, Matrix.toLin' ((x j).2 : Matrix (Fin r) (Fin r) ℂ) v ∈ V)) :
    V = ⊥ ∨ V = ⊤ := by
  let P : invariantSubmoduleSubgroup V :=
    (List.ofFn fun j =>
      ⁅(⟨(x j).1, (hV j).1⟩ : invariantSubmoduleSubgroup V),
        ⟨(x j).2, (hV j).2⟩⁆).prod
  have hdetP : restrictDet V P = 1 := by
    rw [map_list_prod, List.map_ofFn]
    simp [Function.comp_def, restrictDet_commutatorElement, List.ofFn_const]
  have hPval : (P.val : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
    have hsub : (invariantSubmoduleSubgroup V).subtype P =
        (List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod := by
      rw [map_list_prod, List.map_ofFn]
      exact congrArg List.prod <| congrArg List.ofFn <|
        funext fun j => map_commutatorElement (invariantSubmoduleSubgroup V).subtype _ _
    exact (congrArg Subtype.val hsub).trans (mem_relationSet_iff.mp hx)
  have hpow : ζ ^ Module.finrank ℂ V = 1 := by
    have hsmul : LinearMap.restrict (Matrix.toLin' (P.val : Matrix (Fin r) (Fin r) ℂ))
        (fun v hv => P.property v hv) = ζ • (LinearMap.id : V →ₗ[ℂ] V) :=
      LinearMap.ext fun ⟨v, hv⟩ => Subtype.ext (by simp [hPval])
    simpa [restrictDet, hsmul, LinearMap.det_smul, LinearMap.det_id] using hdetP
  have hdvd : r ∣ Module.finrank ℂ V := (hζ.pow_eq_one_iff_dvd _).mp hpow
  have hle : Module.finrank ℂ V ≤ r := by
    simpa [Module.finrank_fin_fun] using Submodule.finrank_le V
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ V) with h0 | hpos
  · exact Or.inl (Submodule.finrank_eq_zero.mp h0)
  · have hge : r ≤ Module.finrank ℂ V := Nat.le_of_dvd hpos hdvd
    exact Or.inr <| Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)

/-- **Schur's lemma for the twisted relation set.** For a primitive `r`-th root of unity `ζ`,
every complex `r × r` matrix commuting with all entries of a solution `x ∈ relationSet r ζ g` is
a scalar matrix. -/
theorem exists_eq_smul_one_of_commute_relationSet {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) (M : Matrix (Fin r) (Fin r) ℂ)
    (hM : ∀ j, Commute M ((x j).1 : Matrix (Fin r) (Fin r) ℂ) ∧
      Commute M ((x j).2 : Matrix (Fin r) (Fin r) ℂ)) :
    ∃ c : ℂ, M = c • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨0, Subsingleton.elim _ _⟩
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' M)
  have hne : Module.End.eigenspace (Matrix.toLin' M) μ ≠ ⊥ := hμ
  have hinv : ∀ j,
      (∀ v ∈ Module.End.eigenspace (Matrix.toLin' M) μ,
        Matrix.toLin' ((x j).1 : Matrix (Fin r) (Fin r) ℂ) v ∈
          Module.End.eigenspace (Matrix.toLin' M) μ) ∧
      (∀ v ∈ Module.End.eigenspace (Matrix.toLin' M) μ,
        Matrix.toLin' ((x j).2 : Matrix (Fin r) (Fin r) ℂ) v ∈
          Module.End.eigenspace (Matrix.toLin' M) μ) := fun j =>
    ⟨Module.End.mapsTo_genEigenspace_of_comm
        ((hM j).1.map (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin r))) μ 1,
     Module.End.mapsTo_genEigenspace_of_comm
        ((hM j).2.map (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin r))) μ 1⟩
  have htop : Module.End.eigenspace (Matrix.toLin' M) μ = ⊤ :=
    (eq_bot_or_eq_top_of_invariant_relationSet hζ hx _ hinv).resolve_left hne
  refine ⟨μ, Matrix.toLin'.injective <| LinearMap.ext fun v => ?_⟩
  have hv : v ∈ Module.End.eigenspace (Matrix.toLin' M) μ := by
    rw [htop]
    trivial
  simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.mp hv

/-- **Vanishing of the trace-free infinitesimal stabilizer.** For a primitive `r`-th root of unity
`ζ`, every trace-free complex matrix commuting with all entries of a solution
`x ∈ relationSet r ζ g` vanishes. -/
theorem eq_zero_of_commute_relationSet_of_trace_eq_zero {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) (M : Matrix (Fin r) (Fin r) ℂ)
    (hM : ∀ j, Commute M ((x j).1 : Matrix (Fin r) (Fin r) ℂ) ∧
      Commute M ((x j).2 : Matrix (Fin r) (Fin r) ℂ))
    (htr : M.trace = 0) : M = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Subsingleton.elim _ _
  obtain ⟨c, rfl⟩ := exists_eq_smul_one_of_commute_relationSet hζ hx M hM
  have hc : (r : ℂ) * c = 0 := by
    simpa [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, mul_comm] using htr
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc0 : c = 0 := (mul_eq_zero.mp hc).resolve_left hr0
  simp [hc0]

/-- Every element of `SU(r)` commuting with all entries of a solution of the twisted relation is
central; see `conjAct_smul_relationSet_eq_self_iff` for the equality of `SU(r)`-stabilizers with
the center and `psu_smul_relationSet_eq_self_iff` / `stabilizer_psu_relationSet_eq_bot` for
freeness of the effective `PSU(r)` action. -/
theorem relationSet_stabilizer_central (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (g : ℕ) (x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ ×
      Matrix.specialUnitaryGroup (Fin r) ℂ) (hx : x ∈ relationSet r ζ g)
    (u : Matrix.specialUnitaryGroup (Fin r) ℂ)
    (hu : ∀ j, Commute u (x j).1 ∧ Commute u (x j).2) :
    u ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) := by
  have hM : ∀ j, Commute (u : Matrix (Fin r) (Fin r) ℂ) ((x j).1 : Matrix (Fin r) (Fin r) ℂ) ∧
      Commute (u : Matrix (Fin r) (Fin r) ℂ) ((x j).2 : Matrix (Fin r) (Fin r) ℂ) := fun j =>
    ⟨congrArg Subtype.val (hu j).1.eq, congrArg Subtype.val (hu j).2.eq⟩
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_commute_relationSet hζ hx u hM
  rw [Matrix.specialUnitaryGroup.mem_center_iff]
  refine ⟨c, ?_, ?_⟩
  · have hdet := congrArg Matrix.det hc
    simpa [Matrix.det_smul, (mem_specialUnitaryGroup_iff.mp u.property).2] using hdet.symm
  · rw [hc]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

/-- An element `u ∈ SU(r)` stabilizes `x : relationSet r ζ g` under simultaneous conjugation if and
only if `u` lies in the center of `SU(r)`. -/
theorem conjAct_smul_relationSet_eq_self_iff {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {g : ℕ} (x : relationSet r ζ g)
    (u : Matrix.specialUnitaryGroup (Fin r) ℂ) :
    ConjAct.toConjAct u • x = x ↔
      u ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) := by
  constructor
  · intro h
    have hcomm {a : Matrix.specialUnitaryGroup (Fin r) ℂ}
        (ha : ConjAct.toConjAct u • a = a) : Commute u a := by
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, mul_inv_eq_iff_eq_mul] at ha
      exact ha
    refine relationSet_stabilizer_central r ζ hζ g x.val x.property u fun j => ?_
    have hj : ConjAct.toConjAct u • x.val j = x.val j := congrFun (congrArg Subtype.val h) j
    exact ⟨hcomm (congrArg Prod.fst hj), hcomm (congrArg Prod.snd hj)⟩
  · exact fun hu => conjAct_smul_eq_self_of_mem_center hu x

/-- **Freeness of the effective `PSU(r)` action.** For a primitive `r`-th root of unity `ζ`, an
element of `PSU(r)` fixes a point `x : relationSet r ζ g` if and only if it is `1`. -/
theorem psu_smul_relationSet_eq_self_iff {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {g : ℕ} (x : relationSet r ζ g)
    (p : (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range) :
    p • x = x ↔ p = 1 := by
  constructor
  · intro hp
    obtain ⟨u, rfl⟩ := toPSL.rangeRestrict_surjective p
    rw [toPSL_rangeRestrict_smul_relationSet, conjAct_smul_relationSet_eq_self_iff hζ x u,
      ← Matrix.specialUnitaryGroup.ker_toPSL_eq_center, MonoidHom.mem_ker] at hp
    exact Subtype.ext hp
  · rintro rfl
    exact one_smul _ x

/-- The `PSU(r)`-stabilizer of every point of `relationSet r ζ g` is trivial when `ζ` is a
primitive `r`-th root of unity. -/
theorem stabilizer_psu_relationSet_eq_bot {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {g : ℕ} (x : relationSet r ζ g) :
    MulAction.stabilizer (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range x = ⊥ := by
  ext p
  simp [MulAction.mem_stabilizer_iff, psu_smul_relationSet_eq_self_iff hζ x p]

end IrreducibilityAndStabilizers

section BoundaryCases

/-- At genus zero, if `r ≥ 1` and `ζ ≠ 1`, the twisted relation set is empty (the empty product of
commutators is `1 ≠ ζ • 1`). -/
theorem relationSet_zero_eq_empty {r : ℕ} (hr : 1 ≤ r) {ζ : ℂ} (hζ : ζ ≠ 1) :
    relationSet r ζ 0 = ∅ := by
  ext x
  simp only [mem_relationSet_zero_iff, Set.mem_empty_iff_false, iff_false]
  intro h
  have h00 := congr_fun₂ h ⟨0, hr⟩ ⟨0, hr⟩
  simp only [Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, mul_one] at h00
  exact hζ h00.symm

/-- For `r ≥ 2` and a primitive `r`-th root of unity `ζ`, the genus-zero relation set is empty. -/
theorem isEmpty_relationSet_zero {r : ℕ} (hr : 2 ≤ r) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    IsEmpty (relationSet r ζ 0) := by
  have hne : ζ ≠ 1 := hζ.ne_one (by omega)
  rw [relationSet_zero_eq_empty (by omega) hne]
  infer_instance

/-- For `r ≥ 2` and a primitive `r`-th root of unity `ζ`, the genus-zero (sphere) moduli is
empty. -/
theorem isEmpty_relationModuli_zero {r : ℕ} (hr : 2 ≤ r) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    IsEmpty (relationModuli r ζ 0) := by
  have : IsEmpty (relationSet r ζ 0) := isEmpty_relationSet_zero hr hζ
  exact ⟨fun q => Quotient.inductionOn q fun x => isEmptyElim x⟩

/-- When `Fin r` is a subsingleton (`r ≤ 1`), `SU(r)` and `relationSet r ζ g` are subsingletons. -/
instance instSubsingletonRelationSet {r : ℕ} [Subsingleton (Fin r)] (ζ : ℂ) (g : ℕ) :
    Subsingleton (relationSet r ζ g) := by
  have : Subsingleton (Matrix.specialUnitaryGroup (Fin r) ℂ) :=
    Matrix.specialUnitaryGroup.toSL_injective.subsingleton
  infer_instance

/-- When `Fin r` is a subsingleton (`r ≤ 1`), `relationModuli r ζ g` is a subsingleton. -/
instance instSubsingletonRelationModuli {r : ℕ} [Subsingleton (Fin r)] (ζ : ℂ) (g : ℕ) :
    Subsingleton (relationModuli r ζ g) :=
  Quotient.instSubsingletonQuotient _

/-- In the untwisted (`ζ = 1`) relation set, the trivial tuple `1` (all entries equal to `1`) is
always a solution. -/
theorem one_mem_relationSet (r g : ℕ) :
    (1 : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ ×
      Matrix.specialUnitaryGroup (Fin r) ℂ) ∈ relationSet r 1 g := by
  rw [mem_relationSet_iff, one_smul]
  have hprod : (List.ofFn fun _ : Fin g =>
      ⁅(1 : Matrix.specialUnitaryGroup (Fin r) ℂ),
        (1 : Matrix.specialUnitaryGroup (Fin r) ℂ)⁆).prod = 1 := by
    simp [List.ofFn_const]
  exact congrArg Subtype.val hprod

/-- At rank one with `ζ = 1`, the relation set is nonempty in every genus. -/
theorem nonempty_relationSet_rank_one {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 1) (g : ℕ) :
    Nonempty (relationSet 1 ζ g) :=
  ⟨⟨1, by rw [IsPrimitiveRoot.one_right_iff.mp hζ]; exact one_mem_relationSet 1 g⟩⟩

/-- At rank one with a primitive `1`-st root of unity (`ζ = 1`), the moduli space is a point in
every genus. -/
theorem relationModuli_rank_one {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 1) (g : ℕ) :
    Nonempty (relationModuli 1 ζ g) ∧ Subsingleton (relationModuli 1 ζ g) := by
  obtain ⟨x⟩ := nonempty_relationSet_rank_one hζ g
  exact ⟨⟨Quotient.mk _ x⟩, inferInstance⟩

/-- At rank one with `ζ = 1`, the moduli space is simply connected in every genus. -/
theorem simplyConnectedSpace_relationModuli_rank_one {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 1) (g : ℕ) :
    SimplyConnectedSpace (relationModuli 1 ζ g) := by
  -- `Subsingleton` is inferred via `instSubsingletonRelationModuli`; only `Nonempty` is needed.
  have : Nonempty (relationModuli 1 ζ g) := (relationModuli_rank_one hζ g).1
  exact SimplyConnectedSpace.ofContractible _

end BoundaryCases

section CentralTwistAction

/-- Multiplying the entries of a solution `x ∈ relationSet r ζ g` by central elements of `SU(r)`
preserves the commutator product and hence preserves `relationSet r ζ g`. -/
theorem center_mul_mem_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (ε : Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) :
    (fun j => ((ε j).1.val * (x j).1, (ε j).2.val * (x j).2)) ∈ relationSet r ζ g := by
  rw [mem_relationSet_iff] at hx ⊢
  have hcomm (j : Fin g) :
      ⁅(ε j).1.val * (x j).1, (ε j).2.val * (x j).2⁆ = ⁅(x j).1, (x j).2⁆ := by
    have h1 := Subgroup.mem_center_iff.mp (ε j).1.property
    have h2 := Subgroup.mem_center_iff.mp (ε j).2.property
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_mul_comm.mpr (h1 _).symm, mul_one, ← h1 _,
      mul_inv_cancel_right, commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_mul_comm.mpr (h2 _), one_mul, ← h2 _, mul_inv_cancel_right]
  simpa [hcomm] using hx

/-- The central-twist action of `(Z(SU(r)) × Z(SU(r)))^g` (representing `H¹(X; μ_r)`) on
`relationSet r ζ g`, multiplying each entry `(A_j, B_j)` by `(z_{1,j}, z_{2,j})`. -/
instance instMulActionCenterTwistRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction
      (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationSet r ζ g) where
  smul ε x := ⟨fun j => ((ε j).1.val * (x.val j).1, (ε j).2.val * (x.val j).2),
    center_mul_mem_relationSet ε x.property⟩
  one_smul _ := Subtype.ext <| funext fun _ => Prod.ext (one_mul _) (one_mul _)
  mul_smul _ _ _ := Subtype.ext <| funext fun _ => Prod.ext (mul_assoc _ _ _) (mul_assoc _ _ _)

@[simp]
theorem coe_centerTwist_smul_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (ε : Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (x : relationSet r ζ g) (j : Fin g) :
    ((ε • x : relationSet r ζ g).val j) =
      ((ε j).1.val * (x.val j).1, (ε j).2.val * (x.val j).2) :=
  (rfl)

instance instContinuousSMulCenterTwistRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousSMul
      (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationSet r ζ g) where
  continuous_smul := by
    have hcoord (j : Fin g)
        (π₁ : Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
            Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) →
          Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (hπ₁ : Continuous π₁)
        (π₂ : Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ →
          Matrix.specialUnitaryGroup (Fin r) ℂ) (hπ₂ : Continuous π₂) :
        Continuous fun p :
          (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
            Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) × relationSet r ζ g =>
          (π₁ (p.1 j)).val * π₂ (p.2.val j) :=
      (continuous_subtypeVal.comp (hπ₁.comp ((continuous_apply j).comp continuous_fst))).mul
        (hπ₂.comp ((continuous_apply j).comp (continuous_subtypeVal.comp continuous_snd)))
    exact continuous_induced_rng.mpr (continuous_pi fun j =>
      (hcoord j Prod.fst continuous_fst Prod.fst continuous_fst).prodMk
        (hcoord j Prod.snd continuous_snd Prod.snd continuous_snd))

/-- Central twists commute with simultaneous `SU(r)`-conjugation on `relationSet r ζ g`. -/
instance instSMulCommClassCenterTwistConjAct (r : ℕ) (ζ : ℂ) (g : ℕ) :
    SMulCommClass
      (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationSet r ζ g) where
  smul_comm ε u x := by
    have hcoord (z : Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
        (a : Matrix.specialUnitaryGroup (Fin r) ℂ) :
        z.val * (u • a) = u • (z.val * a) := by
      rw [ConjAct.smul_def, ConjAct.smul_def, ← mul_assoc, ← mul_assoc,
        ← Subgroup.mem_center_iff.mp z.property (ConjAct.ofConjAct u),
        mul_assoc (ConjAct.ofConjAct u)]
    refine Subtype.ext <| funext fun j => ?_
    simp only [coe_centerTwist_smul_relationSet, coe_conjAct_smul_relationSet, Pi.smul_apply,
      Prod.ext_iff, Prod.smul_fst, Prod.smul_snd]
    exact ⟨hcoord (ε j).1 (x.val j).1, hcoord (ε j).2 (x.val j).2⟩

/-- The induced central-twist action of `(Z(SU(r)) × Z(SU(r)))^g` on `relationModuli r ζ g`. -/
instance instMulActionCenterTwistRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction
      (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationModuli r ζ g) where
  smul ε := Quotient.map' (ε • ·) fun _ _ ⟨u, hu⟩ => ⟨u, by
    dsimp only at hu ⊢
    rw [← smul_comm, hu]⟩
  one_smul q := Quotient.inductionOn q fun x => congrArg (Quotient.mk _) (one_smul _ x)
  mul_smul ε₁ ε₂ q := Quotient.inductionOn q fun x => congrArg (Quotient.mk _) (mul_smul ε₁ ε₂ x)

@[simp]
theorem centerTwist_smul_relationModuli_mk {r : ℕ} {ζ : ℂ} {g : ℕ}
    (ε : Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (x : relationSet r ζ g) :
    ε • (Quotient.mk _ x : relationModuli r ζ g) = Quotient.mk _ (ε • x) :=
  (rfl)

/-- The central-twist action on `relationModuli r ζ g` is continuous. -/
instance instContinuousSMulCenterTwistRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousSMul
      (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationModuli r ζ g) where
  continuous_smul := by
    rw [← (IsOpenQuotientMap.id.prodMap
      (MulAction.isOpenQuotientMap_quotientMk (Γ := ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
        (T := relationSet r ζ g))).continuous_comp_iff]
    exact (continuous_quot_mk.comp continuous_smul).congr fun ⟨ε, x⟩ =>
      (centerTwist_smul_relationModuli_mk ε x).symm

end CentralTwistAction

end GaugeModuli

end TauCeti

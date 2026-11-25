/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Module.Hom
public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.Kahler
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.CircleLift
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.UnitaryLift
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Basic
public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup
import TauCeti.Analysis.Normed.Module.QuadraticMap
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality

/-!
# The canonical `Spinᶜ` lift of the unitary group

Let `V` be an oriented real inner product space of dimension four with an orthogonal complex
structure `J`, and let `ω` be its Kähler form. Let `W` be a complex Clifford module,
`c(v) = ρ (ι Q v)` with `Q v = -‖v‖²`, and let `W⁺` be its positive half-spinors (the
`1`-eigenspace of the chirality element `Γ`). When `J` induces the orientation `o` and `W` is
nontrivial, the `-2i`-eigenspace of `c₂(ω)` in `W⁺` is nonzero (Taubes's canonical line `ℂ u₀`
when `W⁺` has complex dimension two) and the `2i`-eigenspace is its complement.

An almost Hermitian four-manifold carries a canonical `Spinᶜ` structure, with spinor bundle
`W⁺ = Λ⁰'⁰ ⊕ Λ⁰'²` and determinant line `K⁻¹`. At the level of structure groups it is the
canonical homomorphism `U(2) → Spinᶜ(4)` lifting `U(2) ⊆ SO(4)`, and this file constructs it.
The rotations commuting with `J` form the unitary group `U(V, J)`
(`TauCeti.AlmostComplexStructure.unitaryGroup`). The elements of `Spinᶜ(4)` acting trivially on
the `-2i`-eigenspace of `c₂(ω)` in `W⁺` form a subgroup
(`TauCeti.SeibergWitten.canonicalLineFixingSubgroup`), and for any nontrivial complex Clifford
module `W` (no Hermitian structure, finite dimensionality, or rank-two assumption is needed) the
rotation homomorphism `Spinᶜ(4) → SO(4)` maps this subgroup isomorphically onto `U(V, J)`:

* Its rotations commute with `J`. On the `-2i`-eigenspace Clifford multiplication turns `J` into
  `i`, `c(J v) u = i c(v) u`
  (`TauCeti.AlmostComplexStructure.ι_apply_apply_of_bivectorExterior_apply`). Clifford
  equivariance then gives `c(A J v) u = c(J A v) u`, and `c(w) u ≠ 0` for `w ≠ 0` and `u ≠ 0`.
* It meets the kernel of the rotation homomorphism trivially, since that kernel is the twisting
  circle `U(1) ⊆ Spinᶜ(4)`, which acts on the `-2i`-eigenspace by scalars.
* It maps onto `U(V, J)`. Any nonzero `-2i`-eigenvector `u ∈ W⁺` generates a four-dimensional
  `Cl(Q)`-invariant submodule `span {u, c(e₀) c(e₂) u, c(e₀) u, c(e₂) u}` whose positive
  half-spinors have dimension two. Comparing the determinant character on that submodule with the
  action of the quaternionic frame lift `OrthonormalBasis.spinCUnitary` shows that
  `e.spinCUnitary g` acts on `u` by a square root of unity, hence fixes `u` since every element of
  `U(2)` is a square (`TauCeti.SeibergWitten.spinCUnitary_mem_canonicalLineFixingSubgroup`).

The inverse isomorphism is the canonical lift `TauCeti.SeibergWitten.unitaryLift`. Its
determinant character is the scalar by which any element fixing the `-2i`-eigenspace acts on the
`2i`-eigenspace
(`spinCGroupHalfSpinRep_apply_eq_det_smul_of_mem_canonicalLineFixingSubgroup_of_bivectorExterior`),
proved via the same four-dimensional invariant submodule with no dimension or orientation
assumption on `W`. For a unitary frame `(e₀, e₁, e₂, e₃)`, the canonical lift of the rotations of
the complex line `⟨e₂, e₃⟩` is the `Spinᶜ` lift `CliffordAlgebra.spinCCircle` of the rotations of
that oriented plane (`TauCeti.SeibergWitten.unitaryLift_toSpecialOrthogonal_spinCCircle`).

**Charge conjugation.** A conjugate-linear isomorphism `j : W → W'` of Clifford modules commuting
with Clifford multiplication, such as the quaternionic structure of the spinors, exchanges the
`-2i`- and `2i`-eigenspaces of `c₂(ω)` and intertwines `x` with its charge conjugate
`spinCGroup.chargeConj x`. So if `x` fixes the `-2i`-eigenspace of `W⁺`, its charge conjugate
fixes the `2i`-eigenspace of `W'⁺` and acts on the `-2i`-eigenspace of `W'⁺` by `(det x)⁻¹`. For
the canonical lift this is the representation-level form of the identification of the conjugate of
the canonical `Spinᶜ` structure, with positive spinors `Λ⁰'⁰ ⊕ Λ⁰'²`, with its twist by the
canonical line `K = (Λ⁰'²)⁻¹`.

**The frame model and complex determinant.** Reading `V` as `ℂ²` through the complex coordinates
of a unitary frame `e` (`OrthonormalBasis.complexCoords`), which are the coordinates of the
complex basis `(e₀, e₂)` of `(V, J)`
(`TauCeti.AlmostComplexStructure.basisOfOrthonormalBasisFinFour_equivFun_apply`), a rotation in
`U(V, J)` is a unitary matrix, identifying `U(V, J)` with `U(2)`
(`TauCeti.AlmostComplexStructure.unitaryGroupFrameEquiv`). Through it the canonical lift is the
explicit quaternionic lift `OrthonormalBasis.spinCUnitary` of `U(2)`
(`TauCeti.SeibergWitten.unitaryLift_eq_spinCUnitary`), which needs no spin module. Consequently,
the determinant character of the canonical lift is the complex determinant of `A` as a `ℂ`-linear
map of `(V, J)` (`TauCeti.SeibergWitten.det_unitaryLift`): at the level of structure groups, the
determinant line of the canonical `Spinᶜ` structure is the anticanonical line `K⁻¹ = Λ²_ℂ (T X, J)`.

On the negative half-spinors, Clifford multiplication on `u` in the `-2i`-eigenspace intertwines
`A` with the action of its canonical lift
(`TauCeti.SeibergWitten.spinCGroupHalfSpinRep_unitaryLift_halfSpinCliffordMul`). On the positive
half-spinors, the canonical lift sends `c(v) c(w) u` to `c(A v) c(A w) u`
(`TauCeti.SeibergWitten.coe_spinCGroupHalfSpinRep_unitaryLift_apply_of_coe_eq`). With the formula
for `c(v) c(w) u` in `TauCeti.LinearAlgebra.CliffordAlgebra.Kahler`
(`TauCeti.AlmostComplexStructure.ι_apply_ι_apply_of_bivectorExterior_apply`), this gives the
Clifford algebra behind the splitting `W⁺ = Λ⁰'⁰ ⊕ Λ⁰'²` of the canonical `Spinᶜ` structure.

**Continuity.** For the quotient topology on `Spinᶜ(4)` and the topology of `U(V, J)` as a
subgroup of the linear automorphisms of `V`, the canonical lift is continuous
(`TauCeti.SeibergWitten.continuous_unitaryLift`). For any complex Clifford module `W` (with no
topology on `W`), each cyclic subspace `ρ(Cl(Q)) ψ` is finite-dimensional, so the equations
`x ψ = ψ` cut out a closed subgroup (`TauCeti.SeibergWitten.isClosed_canonicalLineFixingSubgroup`),
hence compact since `Spinᶜ(4)` is. The rotation homomorphism is continuous and `U(V, J)` is
Hausdorff, so its restriction to the subgroup is a homeomorphism onto `U(V, J)`, whose inverse is
the canonical lift. Continuity is the hypothesis needed to extend principal bundles along the
canonical lift as a homomorphism of structure groups.

## Main definitions

* `TauCeti.SeibergWitten.canonicalLineFixingSubgroup o ρ J hQ₀`: the elements of `Spinᶜ(4)`
  acting trivially on the `-2i`-eigenspace of `c₂(ω)` in `W⁺`.
* `TauCeti.SeibergWitten.canonicalLineFixingSubgroupEquiv`: the rotation homomorphism, as an
  isomorphism of that subgroup onto `U(V, J)`.
* `TauCeti.SeibergWitten.unitaryLift`: the canonical lift `U(V, J) → Spinᶜ(4)`.
* `TauCeti.SeibergWitten.canonicalLineFixingSubgroupContinuousMulEquiv`: the rotation
  homomorphism, as an isomorphism of topological groups from that subgroup onto `U(V, J)`.
* `TauCeti.SeibergWitten.unitaryLiftContinuousMonoidHom`: the canonical lift as a continuous
  homomorphism.

## Main results

* `TauCeti.SeibergWitten.isClosed_canonicalLineFixingSubgroup`: the subgroup fixing the canonical
  eigenspace is closed in `Spinᶜ(4)`.
* `TauCeti.SeibergWitten.spinCUnitary_mem_canonicalLineFixingSubgroup` and
  `TauCeti.SeibergWitten.spinCCircle_mem_canonicalLineFixingSubgroup`: the quaternionic frame lift
  `e.spinCUnitary` and the plane lift `spinCCircle` on `⟨e₂, e₃⟩` fix the canonical eigenspace.
* `toSpecialOrthogonal_mem_unitaryGroup_of_mem_canonicalLineFixingSubgroup`,
  `eq_one_of_mem_canonicalLineFixingSubgroup_of_toSpecialOrthogonal_eq_one` and
  `exists_mem_canonicalLineFixingSubgroup_toSpecialOrthogonal_eq_of_mem_unitaryGroup`: the three
  steps combined in `TauCeti.SeibergWitten.canonicalLineFixingSubgroupEquiv`.
* `TauCeti.SeibergWitten.toSpecialOrthogonal_unitaryLift` and
  `TauCeti.SeibergWitten.eq_unitaryLift_iff`: the canonical lift lifts `U(V, J) ⊆ SO(4)`, and is
  the unique such lift fixing the canonical eigenspace.
* `spinCGroupHalfSpinRep_apply_eq_det_smul_of_mem_canonicalLineFixingSubgroup_of_bivectorExterior`:
  an element fixing the canonical eigenspace acts on the complementary eigenspace by its
  determinant character.
* `TauCeti.SeibergWitten.spinCGroupHalfSpinRep_unitaryLift_halfSpinCliffordMul` and
  `TauCeti.SeibergWitten.coe_spinCGroupHalfSpinRep_unitaryLift_apply_of_coe_eq`: the action of the
  canonical lift on `c(v) u` in `W⁻` and `c(v) c(w) u` in `W⁺`.
* `TauCeti.SeibergWitten.unitaryLift_unitaryGroupFrameEquiv`,
  `TauCeti.SeibergWitten.unitaryLift_eq_spinCUnitary`,
  `TauCeti.SeibergWitten.unitaryLift_toSpecialOrthogonal_spinCCircle`, and
  `TauCeti.SeibergWitten.det_unitaryLift`: identification with `e.spinCUnitary` and `spinCCircle`,
  and equality of the determinant character with the complex determinant.
* `TauCeti.SeibergWitten.continuous_unitaryLift`: the canonical lift is continuous.
* `spinCGroupHalfSpinRep_chargeConj_apply_eq_self_of_mem_canonicalLineFixingSubgroup` and
  `spinCGroupHalfSpinRep_chargeConj_apply_eq_inv_det_smul_of_mem_canonicalLineFixingSubgroup`:
  for a conjugate-linear Clifford intertwiner `j : W → W'`, the charge conjugate of an element
  fixing the canonical eigenspace fixes the complementary eigenspace of `W'⁺` and acts on its
  canonical eigenspace by the inverse determinant character.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.4.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

noncomputable section

open CliffordAlgebra Module Module.End
open scoped RealInnerProductSpace

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}

/-- The rotation of the quaternionic frame lift `e.spinCUnitary g` is `unitaryGroupFrameEquiv g`. -/
private theorem toSpecialOrthogonal_spinCUnitary_eq_unitaryGroupFrameEquiv
    {J : AlmostComplexStructure V} {e : OrthonormalBasis (Fin 4) ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hQ₀ : Q ≠ 0)
    (g : Matrix.unitaryGroup (Fin 2) ℂ) :
    spinCGroup.toSpecialOrthogonal Q hQ₀ (e.spinCUnitary hQ hQ₀ g) =
      AlmostComplexStructure.unitaryGroupFrameEquiv hQ h₀ h₂ g := by
  ext v
  exact (e.complexCoords 2).injective
    ((e.complexCoords_toSpecialOrthogonal_spinCUnitary_apply hQ hQ₀ g v).trans
      (AlmostComplexStructure.complexCoords_unitaryGroupFrameEquiv_apply hQ h₀ h₂ g v).symm)

variable [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-! ### The subgroup of `Spinᶜ(4)` fixing the canonical eigenspace -/

section FixingSubgroup

variable {J : AlmostComplexStructure V}

variable (o ρ J) in
/-- **The subgroup fixing the canonical eigenspace**: the elements of `Spinᶜ(4)` acting trivially
on the `-2i`-eigenspace of `c₂(ω)` in the positive half-spinors (Taubes's canonical line `ℂ u₀`
when `W⁺` has complex dimension two). -/
def canonicalLineFixingSubgroup (hQ₀ : Q ≠ 0) : Subgroup (spinCGroup Q hQ₀) where
  carrier := {x | ∀ ψ : eigenspace (ρ (chirality Q o)) 1,
    ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • (ψ : W) →
      spinCGroupHalfSpinRep o ρ 1 hQ₀ x ψ = ψ}
  mul_mem' {x y} hx hy ψ hψ := by
    rw [map_mul, mul_apply_eq_comp, hy ψ hψ, hx ψ hψ]
  one_mem' ψ _ := by simp
  inv_mem' {x} hx ψ hψ := by
    conv_lhs => rw [← hx ψ hψ]
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]

/-- Membership in the subgroup fixing the canonical eigenspace. -/
theorem mem_canonicalLineFixingSubgroup_iff {hQ₀ : Q ≠ 0} {x : spinCGroup Q hQ₀} :
    x ∈ canonicalLineFixingSubgroup o ρ J hQ₀ ↔
      ∀ ψ : eigenspace (ρ (chirality Q o)) 1,
        ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • (ψ : W) →
          spinCGroupHalfSpinRep o ρ 1 hQ₀ x ψ = ψ :=
  Iff.rfl

/-- For any fixed spinor `ψ`, the stabilizer `{x | x ψ = ψ}` in `Spinᶜ(4)` is closed, with no
topology assumed on `W`. -/
private theorem isClosed_stabilizer_spinCGroupHalfSpinRep (hQ₀ : Q ≠ 0)
    (ψ : eigenspace (ρ (chirality Q o)) 1) :
    IsClosed {x : spinCGroup Q hQ₀ | spinCGroupHalfSpinRep o ρ 1 hQ₀ x ψ = ψ} := by
  rw [← (QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ₀)).isClosed_preimage]
  let bA := Module.finBasis ℝ (CliffordAlgebra Q)
  let U : Submodule ℂ W := Submodule.span ℂ (Set.range fun i ↦ ρ (bA i) ψ)
  have hmem (a : CliffordAlgebra Q) : ρ a ψ ∈ U := by
    rw [← bA.sum_repr a, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem U fun i _ ↦ ?_
    rw [map_smul, LinearMap.smul_apply]
    exact U.smul_mem (bA.repr a i : ℂ) (Submodule.subset_span ⟨i, rfl⟩)
  have : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let bU := Module.finBasis ℂ U
  let f : CliffordAlgebra Q →ₗ[ℝ] (Fin (finrank ℂ U) → ℂ) :=
    { toFun a := bU.equivFun ⟨ρ a ψ, hmem a⟩
      map_add' a b := by
        rw [← map_add]; congr 1; exact Subtype.ext (by simp)
      map_smul' r a := by
        have h : (⟨ρ (r • a) ψ, hmem (r • a)⟩ : U) = (r : ℂ) • ⟨ρ a ψ, hmem a⟩ :=
          Subtype.ext (by change ρ (r • a) ψ = (r : ℂ) • ρ a ψ; rw [map_smul]; rfl)
        rw [h, map_smul, RingHom.id_apply]
        ext i; simp [Complex.real_smul] }
  have hg : Continuous (fun p : spinGroup Q × Circle ↦ (p.2 : ℂ) • f p.1.val) :=
    (continuous_subtypeVal.comp continuous_snd).smul
      ((IsModuleTopology.continuous_of_linearMap f).comp
        (continuous_subtypeVal.comp continuous_fst))
  have hpre : (QuotientGroup.mk : spinGroup Q × Circle → spinCGroup Q hQ₀) ⁻¹'
      {x | spinCGroupHalfSpinRep o ρ 1 hQ₀ x ψ = ψ} =
      {p : spinGroup Q × Circle | (p.2 : ℂ) • f p.1.val = f 1} := by
    ext ⟨s, z⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, ← spinCGroup.mk_apply,
      spinCGroupHalfSpinRep_mk, Subtype.ext_iff, spinCHalfSpinRep_apply, LinearMap.smul_apply,
      Submodule.coe_smul, coe_halfSpinRep_apply]
    have h1 : f 1 = bU.equivFun ⟨ψ, by simpa using hmem 1⟩ := by simp [f]
    have h2 : (z : ℂ) • f s.val = bU.equivFun ⟨(z : ℂ) • ρ s.val ψ, U.smul_mem _ (hmem s.val)⟩ := by
      change (z : ℂ) • bU.equivFun ⟨ρ s.val ψ, hmem s.val⟩ = _; rw [← map_smul]; rfl
    rw [h1, h2, bU.equivFun.injective.eq_iff, Subtype.ext_iff]
  rw [hpre]
  exact isClosed_eq hg continuous_const

variable (o ρ J) in
/-- **The subgroup fixing the canonical eigenspace is closed** in `Spinᶜ(4)` with its quotient
topology, with no topology assumed on `W`: for each spinor `ψ`, `ρ(Cl(Q)) ψ` lies in a
finite-dimensional complex subspace, so the stabilizer of `ψ` is closed. -/
theorem isClosed_canonicalLineFixingSubgroup (hQ₀ : Q ≠ 0) :
    IsClosed (canonicalLineFixingSubgroup o ρ J hQ₀ : Set (spinCGroup Q hQ₀)) := by
  have hcarrier : (canonicalLineFixingSubgroup o ρ J hQ₀ : Set (spinCGroup Q hQ₀)) =
      ⋂ ψ : eigenspace (ρ (chirality Q o)) 1,
        ⋂ (_ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • (ψ : W)),
          {x | spinCGroupHalfSpinRep o ρ 1 hQ₀ x ψ = ψ} := by
    ext x
    simp only [SetLike.mem_coe, mem_canonicalLineFixingSubgroup_iff, Set.mem_iInter,
      Set.mem_ofPred_eq]
  rw [hcarrier]
  exact isClosed_iInter fun ψ ↦ isClosed_iInter fun _ ↦
    isClosed_stabilizer_spinCGroupHalfSpinRep hQ₀ ψ

/-- A relation `c(w) ψ = μ c(v) ψ` in `W` on a positive half-spinor `ψ` is the same relation
between the half-spin Clifford multiplications `W⁺ → W⁻` by `w` and `v`. -/
private theorem halfSpinCliffordMul_apply_eq_smul {ψ : eigenspace (ρ (chirality Q o)) 1} {μ : ℂ}
    {v w : V} (h : ρ (ι Q w) ψ = μ • ρ (ι Q v) ψ) :
    halfSpinCliffordMul o ρ 1 w ψ = μ • halfSpinCliffordMul o ρ 1 v ψ :=
  Subtype.ext (by simpa using h)

/-- An element of `Spinᶜ(4)` whose rotation commutes with `J` preserves each relation
`c(J v) ψ = μ c(v) ψ`. -/
private theorem ι_apply_apply_spinCGroupHalfSpinRep {hQ₀ : Q ≠ 0} {x : spinCGroup Q hQ₀}
    (hx : spinCGroup.toSpecialOrthogonal Q hQ₀ x ∈ J.unitaryGroup Q) {μ : ℂ}
    {ψ : eigenspace (ρ (chirality Q o)) 1} (hψ : ∀ v, ρ (ι Q (J v)) ψ = μ • ρ (ι Q v) ψ)
    (v : V) :
    ρ (ι Q (J v)) (spinCGroupHalfSpinRep o ρ 1 hQ₀ x ψ) =
      μ • ρ (ι Q v) (spinCGroupHalfSpinRep o ρ 1 hQ₀ x ψ) := by
  obtain ⟨w, rfl⟩ := (spinCGroup.toSpecialOrthogonal Q hQ₀ x : V ≃ₗ[ℝ] V).surjective v
  rw [← AlmostComplexStructure.mem_unitaryGroup_iff.1 hx w, ι_apply_spinCGroupHalfSpinRep_apply,
    ι_apply_spinCGroupHalfSpinRep_apply, halfSpinCliffordMul_apply_eq_smul (hψ w), map_smul,
    Submodule.coe_smul]

/-- The vector `x ψ` of `W` depends only on the vector `ψ` of `W`, not on the eigenspace of the
chirality in which `ψ` is regarded. -/
private theorem coe_spinCGroupHalfSpinRep_apply_congr {hQ₀ : Q ≠ 0} (x : spinCGroup Q hQ₀)
    {ε ε' : ℂ} (h : ε = ε') {ψ : eigenspace (ρ (chirality Q o)) ε}
    {ψ' : eigenspace (ρ (chirality Q o)) ε'} (hψ : (ψ : W) = ψ') :
    (spinCGroupHalfSpinRep o ρ ε hQ₀ x ψ : W) = spinCGroupHalfSpinRep o ρ ε' hQ₀ x ψ' := by
  subst h
  rw [Subtype.ext hψ]

/-- Every unitary orthonormal frame `e` of `J` induces the complex orientation `J.orientation`. -/
private theorem toBasis_orientation_eq_orientation {e : OrthonormalBasis (Fin 4) ℝ V}
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) :
    e.toBasis.orientation = J.orientation Fact.out := by
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂
  rw [AlmostComplexStructure.toBasis_orientation_eq_symplecticForm_orientation_four
      (J.symplecticForm_apply hJ) h₀ h₂,
    ← J.orientation_eq_of_tames (J.symplecticForm_compatible hJ).tames Fact.out]

/-- If `e` is a unitary frame of `J` with opposite orientation `o = -e.toBasis.orientation`, then
`c₂(ω)` vanishes on `W⁺(o)`, so every eigenvector of `c₂(ω)` in `W⁺(o)` with nonzero eigenvalue is
zero. -/
private theorem eq_zero_of_bivectorExterior_apply_of_orientation_eq_neg
    {e : OrthonormalBasis (Fin 4) ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hne : o = -e.toBasis.orientation)
    {μ : ℂ} (hμ : μ ≠ 0) {ψ : eigenspace (ρ (chirality Q o)) 1}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = μ • (ψ : W)) :
    (ψ : W) = 0 := by
  have hchir : chirality Q o = -chirality Q e.toBasis.orientation := by
    rw [hne, chirality_eq_neg_volumeElement, volumeElement_neg_orientation,
      ← chirality_eq_neg_volumeElement]
  have hmem : (ψ : W) ∈ eigenspace (ρ (chirality Q e.toBasis.orientation)) (-1) := by
    have hψ' : ρ (chirality Q o) (ψ : W) = (ψ : W) := by
      simpa using mem_eigenspace_iff.1 ψ.property
    have hneg : -ρ (chirality Q e.toBasis.orientation) (ψ : W) = (ψ : W) := by
      calc -ρ (chirality Q e.toBasis.orientation) (ψ : W)
          = ρ (-chirality Q e.toBasis.orientation) (ψ : W) := by rw [map_neg, LinearMap.neg_apply]
        _ = ρ (chirality Q o) (ψ : W) := congrArg (fun a ↦ ρ a (ψ : W)) hchir.symm
        _ = (ψ : W) := hψ'
    rw [mem_eigenspace_iff, neg_one_smul, ← neg_eq_iff_eq_neg.1 hneg]
  have h23 := map_ι_mul_ι_two_three_apply e hQ ρ rfl hmem
  rw [AlmostComplexStructure.bivectorExterior_kahlerForm hQ h₀ h₂, map_add, LinearMap.add_apply,
    h23, neg_one_smul, add_neg_cancel] at hψ
  exact (smul_eq_zero.1 hψ.symm).resolve_left hμ

/-- `c₂(ω)` anticommutes with `c(e₀) c(e₂)` on `W`. -/
private theorem bivectorExterior_kahlerForm_apply_ι_zero_ι_two {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (w : W) :
    ρ (bivectorExterior Q J.kahlerForm) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) w)) =
      -ρ (ι Q (e 0)) (ρ (ι Q (e 2)) (ρ (bivectorExterior Q J.kahlerForm) w)) := by
  have h01 (x : W) : ρ (ι Q (e 0)) (ρ (ι Q (e 1)) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) x))) =
      -ρ (ι Q (e 0)) (ρ (ι Q (e 2)) (ρ (ι Q (e 0)) (ρ (ι Q (e 1)) x))) := by
    rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 1) (j := 0) (by decide), map_neg,
      e.map_ι_apply_map_ι_apply hQ ρ, neg_neg,
      e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide), map_neg,
      e.map_ι_apply_map_ι_apply hQ ρ, neg_neg,
      e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 1) (j := 2) (by decide)]
  have h23 (x : W) : ρ (ι Q (e 2)) (ρ (ι Q (e 3)) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) x))) =
      -ρ (ι Q (e 0)) (ρ (ι Q (e 2)) (ρ (ι Q (e 2)) (ρ (ι Q (e 3)) x))) := by
    rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 3) (j := 0) (by decide), map_neg,
      e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide), neg_neg,
      e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 3) (j := 2) (by decide), map_neg, map_neg]
  rw [AlmostComplexStructure.bivectorExterior_kahlerForm hQ h₀ h₂]
  simp only [map_add, map_mul, LinearMap.add_apply, mul_apply_eq_comp, h01, h23, neg_add]

/-- If `x` fixes a nonzero `-2i`-eigenvector of `c₂(ω)` in `W⁺`, its rotation commutes with `J`. -/
private theorem toSpecialOrthogonal_mem_unitaryGroup_of_fixed_ne_zero
    {e : OrthonormalBasis (Fin 4) ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) {hQ₀ : Q ≠ 0}
    {x : spinCGroup Q hQ₀} {u : eigenspace (ρ (chirality Q o)) 1} (hu₀ : (u : W) ≠ 0)
    (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • (u : W))
    (hxu : spinCGroupHalfSpinRep o ρ 1 hQ₀ x u = u) :
    spinCGroup.toSpecialOrthogonal Q hQ₀ x ∈ J.unitaryGroup Q := by
  have hcl := AlmostComplexStructure.ι_apply_apply_of_bivectorExterior_apply hQ h₀ h₂ hu
  rw [AlmostComplexStructure.mem_unitaryGroup_iff]
  intro v
  have h1 := ι_apply_spinCGroupHalfSpinRep_apply o ρ 1 hQ₀ x (J v) u
  have h2 := ι_apply_spinCGroupHalfSpinRep_apply o ρ 1 hQ₀ x v u
  rw [hxu] at h1 h2
  rw [halfSpinCliffordMul_apply_eq_smul (ψ := u) (hcl v), map_smul, Submodule.coe_smul,
    ← h2] at h1
  exact map_ι_apply_left_injective ρ (fun w hw ↦ by simpa [hQ] using hw) hu₀
    (h1.trans (hcl _).symm)

/-- **The `Spinᶜ` lift of the rotations of the complex line `⟨e₂, e₃⟩` fixes the canonical
eigenspace.** In the complex orientation, `c₂(ω) = 2 c(e₀) c(e₁)` on `W⁺`, so on the
`-2i`-eigenspace `c(e₀) c(e₁)` acts by `-i`, where `spinCCircle` has weight one; in the opposite
orientation, `c₂(ω)` vanishes on `W⁺`, so the `-2i`-eigenspace is zero. -/
@[simp]
theorem spinCCircle_mem_canonicalLineFixingSubgroup {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hQ₀ : Q ≠ 0)
    (z : Circle) :
    spinCCircle Q hQ₀ (e 2) (e 3) (e.isOrtho_apply hQ (by decide))
      (e.map_apply_mul_map_apply hQ 2 3) z ∈ canonicalLineFixingSubgroup o ρ J hQ₀ := by
  intro ψ hψ
  rcases e.toBasis.orientation_eq_or_eq_neg o with he | hne
  · rw [AlmostComplexStructure.bivectorExterior_kahlerForm hQ h₀ h₂, map_add, LinearMap.add_apply,
      map_ι_mul_ι_two_three_apply e hQ ρ he.symm ψ.property, one_smul] at hψ
    have h : ρ (ι Q (e 0) * ι Q (e 1)) ψ = -Complex.I • (ψ : W) := by
      linear_combination (norm := module) (2⁻¹ : ℂ) • hψ
    exact Subtype.ext
      (coe_spinCGroupHalfSpinRep_one_spinCCircle_apply_of_eq_neg_I_smul hQ₀ e hQ he.symm ρ z h)
  · have h0 : ψ = 0 := Subtype.ext
      (eq_zero_of_bivectorExterior_apply_of_orientation_eq_neg hQ h₀ h₂ hne (by simp) hψ)
    simp [h0]

section InvariantSubmodule

/-- The four-dimensional complex subspace `span {u, c(e₀) c(e₂) u, c(e₀) u, c(e₂) u}` generated
by a `-2i`-eigenvector `u` of `c₂(ω)`. -/
private abbrev canonicalSubmodule (e : OrthonormalBasis (Fin 4) ℝ V) (u : W) : Submodule ℂ W :=
  Submodule.span ℂ {u, ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u), ρ (ι Q (e 0)) u, ρ (ι Q (e 2)) u}

/-- Each frame generator `c(e k)` maps the four generators of `canonicalSubmodule e u` back into
`canonicalSubmodule e u`. -/
private theorem mapsTo_canonicalSubmodule_ι_basis {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    {u : W} (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • u)
    (k : Fin 4) {y : W}
    (hy : y ∈ ({u, ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u), ρ (ι Q (e 0)) u, ρ (ι Q (e 2)) u} : Set W)) :
    ρ (ι Q (e k)) y ∈ canonicalSubmodule (ρ := ρ) e u := by
  set M := canonicalSubmodule (ρ := ρ) e u
  have hb₀M : u ∈ M := Submodule.subset_span (by simp)
  have hb₁M : ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) ∈ M := Submodule.subset_span (by simp)
  have hb₂M : ρ (ι Q (e 0)) u ∈ M := Submodule.subset_span (by simp)
  have hb₃M : ρ (ι Q (e 2)) u ∈ M := Submodule.subset_span (by simp)
  obtain ⟨h1u, h3u⟩ :=
    AlmostComplexStructure.ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply hQ h₀ h₂ hu
  obtain ⟨p10, p30⟩ :=
    AlmostComplexStructure.ι_apply_ι_zero_apply_of_bivectorExterior_apply hQ h₀ h₂ hu
  obtain ⟨p12, p32⟩ :=
    AlmostComplexStructure.ι_apply_ι_two_apply_of_bivectorExterior_apply hQ h₀ h₂ hu
  obtain ⟨p102, p302⟩ :=
    AlmostComplexStructure.ι_apply_ι_zero_apply_ι_two_apply_of_bivectorExterior_apply hQ h₀ h₂ hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl <;>
    match k with
    | 0 => ?_
    | 1 => ?_
    | 2 => ?_
    | 3 => ?_
  · exact hb₂M
  · rw [h1u]; exact M.smul_mem _ hb₂M
  · exact hb₃M
  · rw [h3u]; exact M.smul_mem _ hb₃M
  · rw [e.map_ι_apply_map_ι_apply hQ ρ]; exact M.neg_mem hb₃M
  · rw [p102]; exact M.smul_mem _ hb₃M
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide),
      e.map_ι_apply_map_ι_apply hQ ρ, map_neg, neg_neg]
    exact hb₂M
  · rw [p302]; exact M.smul_mem _ hb₂M
  · rw [e.map_ι_apply_map_ι_apply hQ ρ]; exact M.neg_mem hb₀M
  · rw [p10]; exact M.smul_mem _ hb₀M
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide)]
    exact M.neg_mem hb₁M
  · rw [p30]; exact M.neg_mem (M.smul_mem _ hb₁M)
  · exact hb₁M
  · rw [p12]; exact M.smul_mem _ hb₁M
  · rw [e.map_ι_apply_map_ι_apply hQ ρ]; exact M.neg_mem hb₀M
  · rw [p32]; exact M.smul_mem _ hb₀M

/-- `canonicalSubmodule e u` is invariant under every Clifford element `a : CliffordAlgebra Q`. -/
private theorem mapsTo_canonicalSubmodule {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    {u : W} (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • u)
    (a : CliffordAlgebra Q) :
    ∀ w ∈ canonicalSubmodule (ρ := ρ) e u, ρ a w ∈ canonicalSubmodule (ρ := ρ) e u := by
  set M := canonicalSubmodule (ρ := ρ) e u
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
    intro w hw
    rw [AlgHom.commutes]
    exact M.smul_mem (r : ℂ) hw
  | ι v =>
    intro w hw
    rw [e.map_ι_apply_eq_sum ρ v w]
    refine Submodule.sum_mem M fun k _ ↦ M.smul_mem (⟪e k, v⟫ : ℂ) ?_
    exact Submodule.span_induction (fun _ hy ↦ mapsTo_canonicalSubmodule_ι_basis hQ h₀ h₂ hu k hy)
      (by simp) (fun _ _ _ _ hx hy ↦ by rw [map_add]; exact M.add_mem hx hy)
      (fun c _ _ hx ↦ by rw [map_smul]; exact M.smul_mem c hx) hw
  | mul a b ha hb =>
    intro w hw
    rw [map_mul, mul_apply_eq_comp]
    exact ha _ (hb _ hw)
  | add a b ha hb =>
    intro w hw
    rw [map_add, LinearMap.add_apply]
    exact M.add_mem (ha _ hw) (hb _ hw)

/-- The Clifford action `ρ` restricted to `canonicalSubmodule e u`. -/
private def canonicalSubmoduleAlgHom {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    {u : W} (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • u) :
    CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ (canonicalSubmodule (ρ := ρ) e u) where
  toFun a := (ρ a).restrict (mapsTo_canonicalSubmodule hQ h₀ h₂ hu a)
  map_one' := by ext ⟨w, hw⟩; simp
  map_mul' a b := by ext ⟨w, hw⟩; simp
  map_zero' := by ext ⟨w, hw⟩; simp
  map_add' a b := by ext ⟨w, hw⟩; simp
  commutes' r := by
    ext ⟨w, hw⟩
    change ρ (algebraMap ℝ (CliffordAlgebra Q) r) w = (r : ℂ) • w
    rw [AlgHom.commutes]
    rfl

/-- `c(e₀) c(e₂) u` lies in `W⁺(o)` whenever `u ∈ W⁺(o)`. -/
private theorem ι_zero_ι_two_mem_positive {e : OrthonormalBasis (Fin 4) ℝ V}
    {u : eigenspace (ρ (chirality Q o)) 1} :
    ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) ∈ eigenspace (ρ (chirality Q o)) 1 := by
  rw [← mul_apply_eq_comp, ← map_mul]
  exact mapsTo_genEigenspace_of_comm
    ((commute_chirality_of_mem_even o (ι_mul_ι_mem_evenOdd_zero Q (e 0) (e 2))).map ρ)
    1 1 u.property

/-- Every positive half-spinor in `canonicalSubmodule e u` is a linear combination of `u` and
`c(e₀) c(e₂) u`. -/
private theorem mem_span_positive_canonicalSubmodule {e : OrthonormalBasis (Fin 4) ℝ V}
    {u : eigenspace (ρ (chirality Q o)) 1} {w : W} (hwM : w ∈ canonicalSubmodule (ρ := ρ) e u)
    (hwΓ : ρ (chirality Q o) w = w) :
    ∃ c₀ c₁ : ℂ, w = c₀ • (u : W) + c₁ • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) := by
  rcases Submodule.mem_span_insert.1 hwM with ⟨c₀, _, hw1, rfl⟩
  rcases Submodule.mem_span_insert.1 hw1 with ⟨c₁, _, hw2, rfl⟩
  rcases Submodule.mem_span_insert.1 hw2 with ⟨c₂, _, hw3, rfl⟩
  rcases Submodule.mem_span_singleton.1 hw3 with ⟨c₃, rfl⟩
  have hΓ0 : ρ (chirality Q o) u = u := by simpa using mem_eigenspace_iff.1 u.property
  have hΓ1 : ρ (chirality Q o) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u)) =
      ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) := by
    simpa using mem_eigenspace_iff.1 (ι_zero_ι_two_mem_positive (e := e) (u := u))
  have hΓ2 : ρ (chirality Q o) (ρ (ι Q (e 0)) u) = -ρ (ι Q (e 0)) u := by
    simpa using mem_eigenspace_iff.1 (map_ι_apply_mem_eigenspace_chirality_neg o u.property (e 0))
  have hΓ3 : ρ (chirality Q o) (ρ (ι Q (e 2)) u) = -ρ (ι Q (e 2)) u := by
    simpa using mem_eigenspace_iff.1 (map_ι_apply_mem_eigenspace_chirality_neg o u.property (e 2))
  simp only [map_add, map_smul, hΓ0, hΓ1, hΓ2, hΓ3] at hwΓ
  have h23 : c₂ • ρ (ι Q (e 0)) u + c₃ • ρ (ι Q (e 2)) u = 0 :=
    (smul_eq_zero.1 (show (2 : ℂ) • (c₂ • ρ (ι Q (e 0)) u + c₃ • ρ (ι Q (e 2)) u) = 0 by
      linear_combination (norm := module) -hwΓ)).resolve_left two_ne_zero
  exact ⟨c₀, c₁, by linear_combination (norm := module) h23⟩

/-- For a nonzero `-2i`-eigenvector `u ∈ W⁺(o)` of `c₂(ω)`, `(u, c(e₀) c(e₂) u)` is a `ℂ`-basis of
the positive half-spinors of `canonicalSubmodule e u`. -/
private def canonicalSubmodulePositiveBasis {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    {u : eigenspace (ρ (chirality Q o)) 1} (hu₀ : (u : W) ≠ 0)
    (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • (u : W)) :
    Basis (Fin 2) ℂ
      (eigenspace (canonicalSubmoduleAlgHom hQ h₀ h₂ hu (chirality Q o)) 1) := by
  let M := canonicalSubmodule (ρ := ρ) e u
  let ρM := canonicalSubmoduleAlgHom hQ h₀ h₂ hu
  let b₁ : W := ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u)
  have hb₁ω : ρ (bivectorExterior Q J.kahlerForm) b₁ = (2 * Complex.I) • b₁ := by
    open AlmostComplexStructure in
    exact bivectorExterior_kahlerForm_apply_ι_apply_ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hu
  have hb₁ne : b₁ ≠ 0 := fun h ↦ hu₀ <| by
    have := congrArg (fun w ↦ ρ (ι Q (e 2)) (ρ (ι Q (e 0)) w)) h
    simpa [b₁, e.map_ι_apply_map_ι_apply hQ ρ] using this
  let v₀ : eigenspace (ρM (chirality Q o)) 1 :=
    ⟨⟨u, Submodule.subset_span (by simp)⟩,
      mem_eigenspace_iff.2 (Subtype.ext (by
        change ρ (chirality Q o) u = (1 : ℂ) • (u : W); exact mem_eigenspace_iff.1 u.property))⟩
  let v₁ : eigenspace (ρM (chirality Q o)) 1 :=
    ⟨⟨b₁, Submodule.subset_span (by simp [b₁])⟩,
      mem_eigenspace_iff.2 (Subtype.ext (by
        change ρ (chirality Q o) b₁ = (1 : ℂ) • b₁
        exact mem_eigenspace_iff.1 (ι_zero_ι_two_mem_positive (e := e) (u := u))))⟩
  refine Basis.mk (v := ![v₀, v₁]) ?_ ?_
  · refine LinearIndependent.pair_iff.2 fun s t hst ↦ ?_
    have h1 : s • (u : W) + t • b₁ = 0 := by
      have := congrArg (fun z : eigenspace (ρM (chirality Q o)) 1 ↦ ((z : M) : W)) hst
      simpa [v₀, v₁, b₁] using this
    have h2 := congrArg (ρ (bivectorExterior Q J.kahlerForm)) h1
    simp only [map_add, map_smul, map_zero, hu, hb₁ω] at h2
    have hs : (-4 * Complex.I * s) • (u : W) = 0 := by
      linear_combination (norm := module) h2 - (2 * Complex.I) • h1
    have ht : (4 * Complex.I * t) • b₁ = 0 := by
      linear_combination (norm := module) h2 + (2 * Complex.I) • h1
    exact ⟨by simpa [hu₀, Complex.I_ne_zero] using smul_eq_zero.1 hs,
      by simpa [hb₁ne, Complex.I_ne_zero] using smul_eq_zero.1 ht⟩
  · intro ⟨⟨w, hwM⟩, hwpos⟩ _
    have hwΓ : ρ (chirality Q o) w = w := by
      simpa [ρM, canonicalSubmoduleAlgHom] using congrArg Subtype.val (mem_eigenspace_iff.1 hwpos)
    obtain ⟨c₀, c₁, rfl⟩ := mem_span_positive_canonicalSubmodule hwM hwΓ
    have heq : (⟨⟨c₀ • (u : W) + c₁ • b₁, hwM⟩, hwpos⟩ : eigenspace (ρM (chirality Q o)) 1) =
        c₀ • v₀ + c₁ • v₁ := by
      ext; simp [v₀, v₁, b₁]
    rw [heq]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

/-- Applying `c(A e₀) c(A e₂)` to a `-2i`-eigenvector `u` of `c₂(ω)`, for
`A = unitaryGroupFrameEquiv g`, scales `c(e₀) c(e₂) u` by `det g`. -/
private theorem ι_apply_ι_apply_unitaryGroupFrameEquiv {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
    {u : W} (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • u)
    (g : Matrix.unitaryGroup (Fin 2) ℂ) :
    let A := (AlmostComplexStructure.unitaryGroupFrameEquiv hQ h₀ h₂ g :
      TauCeti.QuadraticMap.specialOrthogonalGroup Q)
    ρ (ι Q ((A : V ≃ₗ[ℝ] V) (e 0))) (ρ (ι Q ((A : V ≃ₗ[ℝ] V) (e 2))) u) =
      (g : Matrix (Fin 2) (Fin 2) ℂ).det • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) := by
  intro A
  let := J.complexModule
  set B := AlmostComplexStructure.basisOfOrthonormalBasisFinFour h₀ h₂
  rw [AlmostComplexStructure.ι_apply_ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hu]
  have hA_inner (v w : V) : ⟪(A : V ≃ₗ[ℝ] V) v, (A : V ≃ₗ[ℝ] V) w⟫ = ⟪v, w⟫ := by
    have hpol := QuadraticMap.polar_eq_neg_two_inner hQ
    have hAQ : ∀ z, Q ((A : V ≃ₗ[ℝ] V) z) = Q z :=
      QuadraticMap.mem_orthogonalGroup_iff.1
        (QuadraticMap.mem_specialOrthogonalGroup_iff.1 A.property).1
    have hp : QuadraticMap.polar Q ((A : V ≃ₗ[ℝ] V) v) ((A : V ≃ₗ[ℝ] V) w) =
        QuadraticMap.polar Q v w := by simp only [QuadraticMap.polar, ← map_add, hAQ]
    rw [hpol, hpol] at hp; linarith
  have h02 : ⟪(A : V ≃ₗ[ℝ] V) (e 0), (A : V ≃ₗ[ℝ] V) (e 2)⟫ = 0 := by
    rw [hA_inner, e.orthonormal.2 (by decide)]
  have h03 : ⟪(A : V ≃ₗ[ℝ] V) (e 0), J ((A : V ≃ₗ[ℝ] V) (e 2))⟫ = 0 := by
    rw [← AlmostComplexStructure.mem_unitaryGroup_iff.1
        (AlmostComplexStructure.unitaryGroupFrameEquiv hQ h₀ h₂ g).property (e 2),
      h₂, hA_inner, e.orthonormal.2 (by decide)]
  have hcoord (v : V) : B.repr ((A : V ≃ₗ[ℝ] V) v) =
      (g : Matrix (Fin 2) (Fin 2) ℂ).mulVec (B.repr v) := by
    change B.equivFun ((A : V ≃ₗ[ℝ] V) v) = (g : Matrix (Fin 2) (Fin 2) ℂ).mulVec (B.equivFun v)
    rw [AlmostComplexStructure.basisOfOrthonormalBasisFinFour_equivFun_apply,
      AlmostComplexStructure.basisOfOrthonormalBasisFinFour_equivFun_apply]
    exact AlmostComplexStructure.complexCoords_unitaryGroupFrameEquiv_apply hQ h₀ h₂ g v
  have hre0 : B.repr (e 0) = Finsupp.single 0 1 := by
    rw [← AlmostComplexStructure.basisOfOrthonormalBasisFinFour_zero h₀ h₂, B.repr_self]
  have hre2 : B.repr (e 2) = Finsupp.single 1 1 := by
    rw [← AlmostComplexStructure.basisOfOrthonormalBasisFinFour_one h₀ h₂, B.repr_self]
  have hdet : B.repr ((A : V ≃ₗ[ℝ] V) (e 0)) 0 * B.repr ((A : V ≃ₗ[ℝ] V) (e 2)) 1 -
      B.repr ((A : V ≃ₗ[ℝ] V) (e 0)) 1 * B.repr ((A : V ≃ₗ[ℝ] V) (e 2)) 0 =
      (g : Matrix (Fin 2) (Fin 2) ℂ).det := by
    rw [hcoord (e 0), hcoord (e 2), hre0, hre2, Matrix.det_fin_two]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [h02, h03, hdet]
  simp

/-- The half-spin representation on `canonicalSubmodule e u` agrees with that on `W`. -/
private theorem coe_spinCGroupHalfSpinRep_canonicalSubmoduleAlgHom
    {e : OrthonormalBasis (Fin 4) ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hQ₀ : Q ≠ 0)
    {u : W} (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • u)
    (x : spinCGroup Q hQ₀)
    (ψ : eigenspace (canonicalSubmoduleAlgHom hQ h₀ h₂ hu (chirality Q o)) 1)
    (ψ' : eigenspace (ρ (chirality Q o)) 1)
    (hψ : ((ψ : canonicalSubmodule (ρ := ρ) e u) : W) = ψ') :
    ((spinCGroupHalfSpinRep o (canonicalSubmoduleAlgHom hQ h₀ h₂ hu) 1 hQ₀ x ψ :
        canonicalSubmodule (ρ := ρ) e u) : W) =
      (spinCGroupHalfSpinRep o ρ 1 hQ₀ x ψ' : W) := by
  obtain ⟨⟨s, z⟩, rfl⟩ := spinCGroup.mk_surjective Q hQ₀ x
  rw [spinCGroupHalfSpinRep_mk, spinCGroupHalfSpinRep_mk, spinCHalfSpinRep_apply,
    spinCHalfSpinRep_apply, LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul,
    Submodule.coe_smul, Submodule.coe_smul, coe_halfSpinRep_apply, coe_halfSpinRep_apply]
  simp only [canonicalSubmoduleAlgHom, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.restrict_apply, hψ]

/-- An element `x ∈ Spinᶜ(4)` whose rotation commutes with `J` scales a nonzero `-2i`-eigenvector
`u ∈ W⁺(o)` by some complex scalar `c`. -/
private theorem exists_smul_of_mem_unitaryGroup {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hQ₀ : Q ≠ 0)
    {u : eigenspace (ρ (chirality Q o)) 1} (hu₀ : (u : W) ≠ 0)
    (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • (u : W))
    {x : spinCGroup Q hQ₀}
    (hx : spinCGroup.toSpecialOrthogonal Q hQ₀ x ∈ J.unitaryGroup Q) :
    ∃ c : ℂ, (spinCGroupHalfSpinRep o ρ 1 hQ₀ x u : W) = c • (u : W) := by
  let B := canonicalSubmodulePositiveBasis hQ h₀ h₂ hu₀ hu
  have hB0 : ((B 0 : canonicalSubmodule (ρ := ρ) e u) : W) = u := by
    simp [B, canonicalSubmodulePositiveBasis]
  have hB1 : ((B 1 : canonicalSubmodule (ρ := ρ) e u) : W) = ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) := by
    simp [B, canonicalSubmodulePositiveBasis]
  set c := B.repr (spinCGroupHalfSpinRep o (canonicalSubmoduleAlgHom hQ h₀ h₂ hu) 1 hQ₀ x (B 0)) 0
  set d := B.repr (spinCGroupHalfSpinRep o (canonicalSubmoduleAlgHom hQ h₀ h₂ hu) 1 hQ₀ x (B 0)) 1
  have hxu_eq : (spinCGroupHalfSpinRep o ρ 1 hQ₀ x u : W) =
      c • (u : W) + d • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) := by
    rw [← coe_spinCGroupHalfSpinRep_canonicalSubmoduleAlgHom hQ h₀ h₂ hQ₀ hu x (B 0) u hB0,
      ← B.sum_repr (spinCGroupHalfSpinRep o _ 1 hQ₀ x (B 0)), Fin.sum_univ_two]
    simp [hB0, hB1, c, d]
  have hxu_ω : ρ (bivectorExterior Q J.kahlerForm) (spinCGroupHalfSpinRep o ρ 1 hQ₀ x u) =
      (-2 * Complex.I) • (spinCGroupHalfSpinRep o ρ 1 hQ₀ x u : W) := by
    have hcl := ι_apply_apply_spinCGroupHalfSpinRep hx
      (AlmostComplexStructure.ι_apply_apply_of_bivectorExterior_apply hQ h₀ h₂ hu)
    simpa [mul_assoc] using
      AlmostComplexStructure.bivectorExterior_apply_eq_smul_of_ι_one_apply_of_ι_three_apply
        hQ h₀ h₂ (h₀ ▸ hcl (e 0)) (h₂ ▸ hcl (e 2))
  have hb₁ω : ρ (bivectorExterior Q J.kahlerForm) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u)) =
      (2 * Complex.I) • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) := by
    open AlmostComplexStructure in
    exact bivectorExterior_kahlerForm_apply_ι_apply_ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hu
  have hb₁ne : ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) ≠ 0 := fun h ↦ hu₀ <| by
    have := congrArg (fun w ↦ ρ (ι Q (e 2)) (ρ (ι Q (e 0)) w)) h
    simpa [e.map_ι_apply_map_ι_apply hQ ρ] using this
  rw [hxu_eq, map_add, map_smul, map_smul, hu, hb₁ω] at hxu_ω
  have hd : d = 0 := by
    have h2 : (4 * Complex.I * d) • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) = 0 := by
      linear_combination (norm := module) hxu_ω
    simpa [hb₁ne, Complex.I_ne_zero] using smul_eq_zero.1 h2
  exact ⟨c, by simpa [hd] using hxu_eq⟩

/-- Any `x ∈ Spinᶜ(4)` whose rotation commutes with `J` scales a nonzero `-2i`-eigenvector
`u ∈ W⁺(o)` by some `c : ℂ`, scales `c(e₀) c(e₂) u` by `c * det g` (where `g` is the matrix of
the rotation in the frame `e`), and satisfies `c ^ 2 * det g = det x`. -/
private theorem exists_smul_and_det_of_mem_unitaryGroup {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hQ₀ : Q ≠ 0)
    {u : eigenspace (ρ (chirality Q o)) 1} (hu₀ : (u : W) ≠ 0)
    (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • (u : W))
    {x : spinCGroup Q hQ₀}
    (hx : spinCGroup.toSpecialOrthogonal Q hQ₀ x ∈ J.unitaryGroup Q) :
    let g := (AlmostComplexStructure.unitaryGroupFrameEquiv hQ h₀ h₂).symm ⟨_, hx⟩
    ∃ c : ℂ,
      (spinCGroupHalfSpinRep o ρ 1 hQ₀ x u : W) = c • (u : W) ∧
      (spinCGroupHalfSpinRep o ρ 1 hQ₀ x ⟨ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u),
          ι_zero_ι_two_mem_positive⟩ : W) =
        (c * (g : Matrix (Fin 2) (Fin 2) ℂ).det) • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) ∧
      c ^ 2 * (g : Matrix (Fin 2) (Fin 2) ℂ).det = (spinCGroup.det Q hQ₀ x : ℂ) := by
  intro g
  let ρM := canonicalSubmoduleAlgHom hQ h₀ h₂ hu
  let B := canonicalSubmodulePositiveBasis hQ h₀ h₂ hu₀ hu
  have hM₂ : finrank ℂ (eigenspace (ρM (chirality Q o)) 1) = 2 := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  have hB0 : ((B 0 : canonicalSubmodule (ρ := ρ) e u) : W) = u := by
    simp [B, canonicalSubmodulePositiveBasis]
  have hB1 : ((B 1 : canonicalSubmodule (ρ := ρ) e u) : W) = ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) := by
    simp [B, canonicalSubmodulePositiveBasis]
  obtain ⟨c, hxu⟩ := exists_smul_of_mem_unitaryGroup hQ h₀ h₂ hQ₀ hu₀ hu hx
  have hAg : spinCGroup.toSpecialOrthogonal Q hQ₀ x =
      AlmostComplexStructure.unitaryGroupFrameEquiv hQ h₀ h₂ g :=
    (congrArg Subtype.val ((AlmostComplexStructure.unitaryGroupFrameEquiv hQ h₀ h₂).apply_symm_apply
      ⟨_, hx⟩)).symm
  have hxb₁ : (spinCGroupHalfSpinRep o ρ 1 hQ₀ x
      ⟨ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u), ι_zero_ι_two_mem_positive⟩ : W) =
      (c * (g : Matrix (Fin 2) (Fin 2) ℂ).det) • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) := by
    have h1 := ι_apply_spinCGroupHalfSpinRep_apply o ρ 1 hQ₀ x (e 2) u
    have h2 := ι_apply_spinCGroupHalfSpinRep_apply o ρ (-1) hQ₀ x (e 0)
      (halfSpinCliffordMul o ρ 1 (e 2) u)
    rw [coe_spinCGroupHalfSpinRep_apply_congr x (neg_neg (1 : ℂ))
      (ψ' := ⟨ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u), ι_zero_ι_two_mem_positive⟩) (by simp)] at h2
    rw [← h2, ← h1, hxu, map_smul, map_smul, hAg,
      ι_apply_ι_apply_unitaryGroupFrameEquiv hQ h₀ h₂ hu g, smul_smul]
  have hT0 : spinCGroupHalfSpinRep o ρM 1 hQ₀ x (B 0) = c • B 0 := by
    ext
    simpa [hB0] using (coe_spinCGroupHalfSpinRep_canonicalSubmoduleAlgHom
      hQ h₀ h₂ hQ₀ hu x (B 0) u hB0).trans hxu
  have hT1 : spinCGroupHalfSpinRep o ρM 1 hQ₀ x (B 1) =
      (c * (g : Matrix (Fin 2) (Fin 2) ℂ).det) • B 1 := by
    ext
    simpa [hB1] using (coe_spinCGroupHalfSpinRep_canonicalSubmoduleAlgHom
      hQ h₀ h₂ hQ₀ hu x (B 1) ⟨_, ι_zero_ι_two_mem_positive⟩ hB1).trans hxb₁
  have hdetM := det_spinCGroupHalfSpinRep o ρM 1 hQ₀ hQ hM₂ x
  rw [← LinearMap.det_toMatrix B, Matrix.det_fin_two] at hdetM
  simp only [LinearMap.toMatrix_apply, hT0, hT1, map_smul, B.repr_self, Finsupp.single_eq_same,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_eq_of_ne zero_ne_one,
    Finsupp.single_eq_of_ne one_ne_zero, mul_zero, sub_zero] at hdetM
  exact ⟨c, hxu, hxb₁, by linear_combination hdetM⟩

end InvariantSubmodule

/-- **The quaternionic frame lift fixes the canonical eigenspace** on every complex Clifford
module `W`, with no dimension, orientation, or Hermitian assumption: on any nonzero
`-2i`-eigenvector of `c₂(ω)` in `W⁺`, `e.spinCUnitary h` acts by a square root of unity, and every
element of `U(2)` is a square. -/
@[simp]
theorem spinCUnitary_mem_canonicalLineFixingSubgroup {e : OrthonormalBasis (Fin 4) ℝ V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hQ₀ : Q ≠ 0)
    (g : Matrix.unitaryGroup (Fin 2) ℂ) :
    e.spinCUnitary hQ hQ₀ g ∈ canonicalLineFixingSubgroup o ρ J hQ₀ := by
  obtain ⟨h, rfl⟩ := Matrix.UnitaryGroup.isSquare g
  intro u hu
  by_cases hu₀ : (u : W) = 0
  · have h0 : u = 0 := Subtype.ext hu₀
    simp [h0]
  have hrot := toSpecialOrthogonal_spinCUnitary_eq_unitaryGroupFrameEquiv hQ h₀ h₂ hQ₀ h
  have hx : spinCGroup.toSpecialOrthogonal Q hQ₀ (e.spinCUnitary hQ hQ₀ h) ∈ J.unitaryGroup Q :=
    hrot ▸ (AlmostComplexStructure.unitaryGroupFrameEquiv hQ h₀ h₂ h).property
  obtain ⟨c, hcu, -, hdet⟩ :=
    exists_smul_and_det_of_mem_unitaryGroup hQ h₀ h₂ hQ₀ hu₀ hu hx
  have hg : (AlmostComplexStructure.unitaryGroupFrameEquiv hQ h₀ h₂).symm ⟨_, hx⟩ = h := by
    apply (AlmostComplexStructure.unitaryGroupFrameEquiv hQ h₀ h₂).injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext hrot
  rw [hg, e.det_spinCUnitary hQ hQ₀, Matrix.UnitaryGroup.coe_detCircle] at hdet
  have hdet0 : (h : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [← Matrix.UnitaryGroup.coe_detCircle]
    exact Circle.coe_ne_zero _
  have hc2 : c ^ 2 = 1 := (mul_eq_right₀ hdet0).1 hdet
  have hcu' : spinCGroupHalfSpinRep o ρ 1 hQ₀ (e.spinCUnitary hQ hQ₀ h) u = c • u :=
    Subtype.ext hcu
  rw [map_mul, map_mul, mul_apply_eq_comp, hcu', map_smul, hcu', smul_smul, ← sq, hc2, one_smul]

/-- **Every unitary rotation lifts to the subgroup fixing the canonical eigenspace**, on every
complex Clifford module `W`: in any unitary frame `e`, the quaternionic lift `e.spinCUnitary`
provides the lift. -/
theorem exists_mem_canonicalLineFixingSubgroup_toSpecialOrthogonal_eq_of_mem_unitaryGroup
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (hQ₀ : Q ≠ 0)
    {A : TauCeti.QuadraticMap.specialOrthogonalGroup Q} (hA : A ∈ J.unitaryGroup Q) :
    ∃ x ∈ canonicalLineFixingSubgroup o ρ J hQ₀, spinCGroup.toSpecialOrthogonal Q hQ₀ x = A := by
  obtain ⟨e, h₀, h₂⟩ := AlmostComplexStructure.exists_unitary_orthonormalBasis hJ
  set g := (AlmostComplexStructure.unitaryGroupFrameEquiv hQ h₀ h₂).symm ⟨A, hA⟩
  refine ⟨e.spinCUnitary hQ hQ₀ g,
    spinCUnitary_mem_canonicalLineFixingSubgroup hQ h₀ h₂ hQ₀ g, ?_⟩
  rw [toSpecialOrthogonal_spinCUnitary_eq_unitaryGroupFrameEquiv hQ h₀ h₂ hQ₀ g]
  exact congrArg Subtype.val
    ((AlmostComplexStructure.unitaryGroupFrameEquiv hQ h₀ h₂).apply_symm_apply ⟨A, hA⟩)

/-- **The determinant character is the action on the complementary eigenspace.** An element `x` of
`Spinᶜ(4)` fixing the `-2i`-eigenspace of `c₂(ω)` in `W⁺` acts on the complementary
`2i`-eigenspace by its determinant character `det x`, on every complex Clifford module `W`. -/
theorem
    spinCGroupHalfSpinRep_apply_eq_det_smul_of_mem_canonicalLineFixingSubgroup_of_bivectorExterior
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (hQ₀ : Q ≠ 0)
    {x : spinCGroup Q hQ₀} (hx : x ∈ canonicalLineFixingSubgroup o ρ J hQ₀)
    {β : eigenspace (ρ (chirality Q o)) 1}
    (hβ : ρ (bivectorExterior Q J.kahlerForm) β = (2 * Complex.I) • (β : W)) :
    spinCGroupHalfSpinRep o ρ 1 hQ₀ x β = (spinCGroup.det Q hQ₀ x : ℂ) • β := by
  by_cases hβ₀ : (β : W) = 0
  · have h0 : β = 0 := Subtype.ext hβ₀
    simp [h0]
  obtain ⟨e, h₀, h₂⟩ := AlmostComplexStructure.exists_unitary_orthonormalBasis hJ
  let u : eigenspace (ρ (chirality Q o)) 1 :=
    ⟨ρ (ι Q (e 0)) (ρ (ι Q (e 2)) β), ι_zero_ι_two_mem_positive⟩
  have hu₀ : (u : W) ≠ 0 := fun h ↦ hβ₀ <| by
    have := congrArg (fun w ↦ ρ (ι Q (e 2)) (ρ (ι Q (e 0)) w)) h
    simpa [u, e.map_ι_apply_map_ι_apply hQ ρ] using this
  have hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • (u : W) := by
    change ρ (bivectorExterior Q J.kahlerForm) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) β)) = _
    rw [bivectorExterior_kahlerForm_apply_ι_zero_ι_two hQ h₀ h₂, hβ, map_smul, map_smul]
    module
  have hxu : spinCGroupHalfSpinRep o ρ 1 hQ₀ x u = u := hx u hu
  have hxA := toSpecialOrthogonal_mem_unitaryGroup_of_fixed_ne_zero hQ h₀ h₂ hu₀ hu hxu
  obtain ⟨c, hcu, hcb₁, hdet⟩ :=
    exists_smul_and_det_of_mem_unitaryGroup hQ h₀ h₂ hQ₀ hu₀ hu hxA
  have hc : c = 1 := by
    have h1 : (c - 1) • (u : W) = 0 := by rw [sub_smul, ← hcu, hxu, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hu₀)
  have hnegβ : ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u) = -(β : W) := by
    change ρ (ι Q (e 0)) (ρ (ι Q (e 2)) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) β))) = -(β : W)
    rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide), map_neg,
      e.map_ι_apply_map_ι_apply hQ ρ, e.map_ι_apply_map_ι_apply hQ ρ, neg_neg]
  have hsub : (⟨ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u), ι_zero_ι_two_mem_positive⟩ :
      eigenspace (ρ (chirality Q o)) 1) = -β := Subtype.ext hnegβ
  rw [hc, one_pow, one_mul] at hdet
  rw [hc, one_mul, hdet, hsub, map_neg, Submodule.coe_neg, hnegβ, smul_neg] at hcb₁
  exact Subtype.ext (neg_injective hcb₁)

end FixingSubgroup

/-! ### Charge conjugation -/

section ChargeConjugation

open scoped ComplexConjugate

variable {J : AlmostComplexStructure V} {W' : Type*} [AddCommGroup W'] [Module ℂ W']
  {ρ' : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W'} (j : W ≃ₗ⋆[ℂ] W')
  (hj : ∀ v w, j (ρ (ι Q v) w) = ρ' (ι Q v) (j w))

include hj in
/-- A conjugate-linear Clifford intertwiner `j : W ≃ W'` carries a positive half-spinor of `W'` in
the `μ`-eigenspace of `c₂(ω)` back to a positive half-spinor of `W` in the `conj μ`-eigenspace. -/
private theorem exists_symm_apply_eq_of_bivectorExterior_apply {μ : ℂ}
    {β : eigenspace (ρ' (chirality Q o)) 1}
    (hβ : ρ' (bivectorExterior Q J.kahlerForm) β = μ • (β : W')) :
    ∃ ψ : eigenspace (ρ (chirality Q o)) 1, (ψ : W) = j.symm β ∧
      ρ (bivectorExterior Q J.kahlerForm) ψ = conj μ • (ψ : W) := by
  have hj' : ∀ v w, j.symm (ρ' (ι Q v) w) = ρ (ι Q v) (j.symm w) := fun v w ↦ by
    rw [j.symm_apply_eq, hj, j.apply_symm_apply]
  have hmem := map_mem_eigenspace_chirality (fun r ↦ Complex.conj_ofReal r)
    (U := j.symm.toLinearMap) hj' β.property
  rw [map_one] at hmem
  refine ⟨⟨j.symm β, hmem⟩, rfl, ?_⟩
  have h := map_apply_of_forall_ιₛₗ (fun r ↦ Complex.conj_ofReal r)
    (U := j.symm.toLinearMap) hj' (bivectorExterior Q J.kahlerForm) β
  simp only [LinearEquiv.coe_coe, hβ, map_smulₛₗ] at h
  exact h.symm

include hj in
/-- **The charge conjugate of an element fixing the canonical eigenspace fixes the complementary
eigenspace.** Let `j : W → W'` be a conjugate-linear isomorphism of Clifford modules commuting
with Clifford multiplication. If `x ∈ Spinᶜ(4)` fixes the `-2i`-eigenspace of `c₂(ω)` in `W⁺`,
then its charge conjugate `spinCGroup.chargeConj x` fixes the `2i`-eigenspace of `c₂(ω)` in `W'⁺`:
`j` exchanges the two eigenspaces and intertwines `x` with its charge conjugate. -/
theorem spinCGroupHalfSpinRep_chargeConj_apply_eq_self_of_mem_canonicalLineFixingSubgroup
    (hQ₀ : Q ≠ 0) {x : spinCGroup Q hQ₀} (hx : x ∈ canonicalLineFixingSubgroup o ρ J hQ₀)
    {β : eigenspace (ρ' (chirality Q o)) 1}
    (hβ : ρ' (bivectorExterior Q J.kahlerForm) β = (2 * Complex.I) • (β : W')) :
    spinCGroupHalfSpinRep o ρ' 1 hQ₀ (spinCGroup.chargeConj Q hQ₀ x) β = β := by
  obtain ⟨ψ, hψj, hψ⟩ := exists_symm_apply_eq_of_bivectorExterior_apply j hj hβ
  have hψ' : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • (ψ : W) := by
    simpa [map_ofNat] using hψ
  refine Subtype.ext ?_
  rw [← map_coe_spinCGroupHalfSpinRep_apply o ρ 1 hQ₀ (j := j.toLinearMap) hj x (ψ := ψ) (ψ' := β)
    (by simp [hψj]), hx ψ hψ']
  simp [hψj]

include hj in
/-- **The charge conjugate of an element fixing the canonical eigenspace acts on the canonical
eigenspace by the inverse determinant.** Let `j : W → W'` be a conjugate-linear isomorphism of
Clifford modules commuting with Clifford multiplication. If `x ∈ Spinᶜ(4)` fixes the
`-2i`-eigenspace of `c₂(ω)` in `W⁺`, then `spinCGroup.chargeConj x` acts on the `-2i`-eigenspace
of `c₂(ω)` in `W'⁺` by `(det x)⁻¹`, the conjugate of the scalar `det x` by which `x` acts on the
complementary eigenspace of `W⁺`. By
`spinCGroupHalfSpinRep_chargeConj_apply_eq_self_of_mem_canonicalLineFixingSubgroup`, it fixes
the `2i`-eigenspace of `W'⁺`. So for `x` the canonical lift of a unitary rotation, the charge
conjugate acts on `W'⁺` as on `K ⊕ Λ⁰'⁰`, with `K = (Λ⁰'²)⁻¹`: the canonical representation
`Λ⁰'⁰ ⊕ Λ⁰'²` tensored with `K`. -/
theorem spinCGroupHalfSpinRep_chargeConj_apply_eq_inv_det_smul_of_mem_canonicalLineFixingSubgroup
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (hQ₀ : Q ≠ 0)
    {x : spinCGroup Q hQ₀} (hx : x ∈ canonicalLineFixingSubgroup o ρ J hQ₀)
    {u : eigenspace (ρ' (chirality Q o)) 1}
    (hu : ρ' (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • (u : W')) :
    spinCGroupHalfSpinRep o ρ' 1 hQ₀ (spinCGroup.chargeConj Q hQ₀ x) u =
      (((spinCGroup.det Q hQ₀ x)⁻¹ : Circle) : ℂ) • u := by
  obtain ⟨ψ, hψj, hψ⟩ := exists_symm_apply_eq_of_bivectorExterior_apply j hj hu
  have hψ' : ρ (bivectorExterior Q J.kahlerForm) ψ = (2 * Complex.I) • (ψ : W) := by
    simpa [map_ofNat] using hψ
  refine Subtype.ext ?_
  rw [← map_coe_spinCGroupHalfSpinRep_apply o ρ 1 hQ₀ (j := j.toLinearMap) hj x (ψ := ψ) (ψ' := u)
    (by simp [hψj]),
    spinCGroupHalfSpinRep_apply_eq_det_smul_of_mem_canonicalLineFixingSubgroup_of_bivectorExterior
      hQ hJ hQ₀ hx hψ']
  simp [hψj, ← Circle.coe_inv_eq_conj]

end ChargeConjugation

/-! ### The canonical lift -/

section Lift

variable [Nontrivial W] {J : AlmostComplexStructure V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
  (ho : J.orientation Fact.out = o) (hQ₀ : Q ≠ 0)

include hQ in
/-- Every nontrivial complex Clifford module has a nonzero positive half-spinor. -/
private theorem exists_ne_zero_positiveHalfSpinor (e : OrthonormalBasis (Fin 4) ℝ V) :
    ∃ ψ : eigenspace (ρ (chirality Q o)) 1, (ψ : W) ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hΓ2 (z : W) : ρ (chirality Q o) (ρ (chirality Q o) z) = z := by
    rw [← mul_apply_eq_comp, ← map_mul, chirality_mul_self o hQ, map_one, one_apply_eq_self]
  by_cases hp : w + ρ (chirality Q o) w = 0
  · have hm : w - ρ (chirality Q o) w ≠ 0 := fun h ↦ hw <|
      (smul_eq_zero.1 (show (2 : ℂ) • w = 0 by
        linear_combination (norm := module) hp + h)).resolve_left two_ne_zero
    have hmem_neg : w - ρ (chirality Q o) w ∈ eigenspace (ρ (chirality Q o)) (-1) := by
      rw [mem_eigenspace_iff, map_sub, hΓ2, neg_one_smul, neg_sub]
    refine ⟨⟨ρ (ι Q (e 0)) (w - ρ (chirality Q o) w), by
      simpa using map_ι_apply_mem_eigenspace_chirality_neg o hmem_neg (e 0)⟩, fun h ↦ hm ?_⟩
    have := congrArg (ρ (ι Q (e 0))) h
    rw [e.map_ι_apply_map_ι_apply hQ ρ, map_zero, neg_eq_zero] at this
    exact this
  · exact ⟨⟨w + ρ (chirality Q o) w, by
      rw [mem_eigenspace_iff, map_add, hΓ2, one_smul, add_comm]⟩, hp⟩

include hQ hJ ho in
/-- Any nontrivial complex Clifford module has a nonzero `-2i`-eigenvector of `c₂(ω)` in `W⁺(o)`
when `J` induces the orientation `o`. -/
private theorem exists_ne_zero_bivectorExterior_apply :
    ∃ u : eigenspace (ρ (chirality Q o)) 1, (u : W) ≠ 0 ∧
      ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • (u : W) := by
  obtain ⟨e, h₀, h₂⟩ := AlmostComplexStructure.exists_unitary_orthonormalBasis hJ
  have he : e.toBasis.orientation = o := (toBasis_orientation_eq_orientation h₀ h₂).trans ho
  obtain ⟨ψ, hψ₀⟩ := exists_ne_zero_positiveHalfSpinor (o := o) (ρ := ρ) hQ e
  have hψ' : ρ (bivectorExterior Q J.kahlerForm) ψ ∈ eigenspace (ρ (chirality Q o)) 1 :=
    mapsTo_genEigenspace_of_comm ((commute_chirality_bivectorExterior o J.kahlerForm).map ρ)
      1 1 ψ.property
  have hω2 : ρ (bivectorExterior Q J.kahlerForm) (ρ (bivectorExterior Q J.kahlerForm) ψ) =
      (-4 : ℂ) • (ψ : W) := by
    have hω (z : eigenspace (ρ (chirality Q o)) 1) :
        ρ (bivectorExterior Q J.kahlerForm) z = (2 : ℂ) • ρ (ι Q (e 0)) (ρ (ι Q (e 1)) z) := by
      rw [AlmostComplexStructure.bivectorExterior_kahlerForm hQ h₀ h₂, map_add, LinearMap.add_apply,
        map_ι_mul_ι_two_three_apply e hQ ρ he z.property, one_smul, map_mul, mul_apply_eq_comp,
        two_smul]
    have h1 := hω ⟨_, hψ'⟩
    change ρ (bivectorExterior Q J.kahlerForm) (ρ (bivectorExterior Q J.kahlerForm) ψ) =
      (2 : ℂ) • ρ (ι Q (e 0)) (ρ (ι Q (e 1)) (ρ (bivectorExterior Q J.kahlerForm) ψ)) at h1
    rw [h1, hω ψ, map_smul, map_smul,
      e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 1) (j := 0) (by decide), map_neg,
      e.map_ι_apply_map_ι_apply hQ ρ, e.map_ι_apply_map_ι_apply hQ ρ, neg_neg]
    module
  set u₁ : W := (ψ : W) + (Complex.I / 2) • ρ (bivectorExterior Q J.kahlerForm) ψ
  set u₂ : W := (ψ : W) - (Complex.I / 2) • ρ (bivectorExterior Q J.kahlerForm) ψ
  by_cases hu₁ : u₁ = 0
  · have hu₂ : u₂ ≠ 0 := fun h ↦ hψ₀ <|
      (smul_eq_zero.1 (show (2 : ℂ) • (ψ : W) = 0 by
        linear_combination (norm := module) hu₁ + h)).resolve_left two_ne_zero
    have hu₂_pos : u₂ ∈ eigenspace (ρ (chirality Q o)) 1 :=
      Submodule.sub_mem _ ψ.property (Submodule.smul_mem _ _ hψ')
    have hu₂_ω : ρ (bivectorExterior Q J.kahlerForm) u₂ = (2 * Complex.I) • u₂ := by
      simp only [u₂, map_sub, map_smul, hω2]
      match_scalars
      · linear_combination Complex.I_sq
      · ring
    refine ⟨⟨ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₂), ι_zero_ι_two_mem_positive (u := ⟨u₂, hu₂_pos⟩)⟩,
      fun h ↦ hu₂ ?_, ?_⟩
    · have := congrArg (fun z ↦ ρ (ι Q (e 2)) (ρ (ι Q (e 0)) z)) h
      simpa [e.map_ι_apply_map_ι_apply hQ ρ] using this
    · change ρ (bivectorExterior Q J.kahlerForm) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₂)) = _
      rw [bivectorExterior_kahlerForm_apply_ι_zero_ι_two hQ h₀ h₂, hu₂_ω, map_smul, map_smul]
      module
  · refine ⟨⟨u₁, Submodule.add_mem _ ψ.property (Submodule.smul_mem _ _ hψ')⟩, hu₁, ?_⟩
    simp only [u₁, map_add, map_smul, hω2]
    match_scalars
    · linear_combination Complex.I_sq
    · ring

include hQ hJ ho in
/-- **An element fixing the canonical eigenspace rotates `V` complex linearly**: its rotation
commutes with `J`. -/
theorem toSpecialOrthogonal_mem_unitaryGroup_of_mem_canonicalLineFixingSubgroup
    {x : spinCGroup Q hQ₀} (hx : x ∈ canonicalLineFixingSubgroup o ρ J hQ₀) :
    spinCGroup.toSpecialOrthogonal Q hQ₀ x ∈ J.unitaryGroup Q := by
  obtain ⟨e, h₀, h₂⟩ := AlmostComplexStructure.exists_unitary_orthonormalBasis hJ
  obtain ⟨u, hu₀, hu⟩ := exists_ne_zero_bivectorExterior_apply (ρ := ρ) hQ hJ ho
  exact toSpecialOrthogonal_mem_unitaryGroup_of_fixed_ne_zero hQ h₀ h₂ hu₀ hu (hx u hu)

include hQ hJ ho in
/-- **Only the identity fixes the canonical eigenspace and acts trivially on `V`**: the kernel of
the rotation homomorphism is the twisting circle, which acts on the canonical eigenspace by
scalars. -/
theorem eq_one_of_mem_canonicalLineFixingSubgroup_of_toSpecialOrthogonal_eq_one
    {x : spinCGroup Q hQ₀} (hx : x ∈ canonicalLineFixingSubgroup o ρ J hQ₀)
    (h1 : spinCGroup.toSpecialOrthogonal Q hQ₀ x = 1) : x = 1 := by
  have hQn : Q.Nondegenerate := QuadraticForm.nondegenerate_of_eq_neg_norm_sq hQ
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = 4)
  -- The kernel of the rotation homomorphism is the twisting circle.
  obtain ⟨w, rfl⟩ : ∃ w : Circle, spinCGroup.ofCircle Q hQ₀ w = x := by
    obtain ⟨⟨s, z⟩, rfl⟩ := spinCGroup.mk_surjective Q hQ₀ x
    rw [spinCGroup.toSpecialOrthogonal_mk] at h1
    rcases (mem_ker_spinToSpecialOrthogonal_iff Q hQn s).1 h1 with rfl | rfl
    · exact ⟨z, by rw [← spinCGroup.ofSpin_mul_ofCircle, map_one, one_mul]⟩
    · exact ⟨-1 * z, by rw [← spinCGroup.ofSpin_mul_ofCircle, spinCGroup.ofSpin_negOne, map_mul]⟩
  -- It acts on a nonzero vector of the canonical eigenspace by `w`.
  obtain ⟨u, hu₀, hu⟩ := exists_ne_zero_bivectorExterior_apply (ρ := ρ) hQ hJ ho
  have h := congrArg Subtype.val (hx u hu)
  rw [spinCGroupHalfSpinRep_ofCircle, LinearMap.smul_apply, one_apply_eq_self,
    Submodule.coe_smul] at h
  have hw : (w : ℂ) = 1 := by
    have h' : ((w : ℂ) - 1) • (u : W) = 0 := by rw [sub_smul, h, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right hu₀)
  rw [Circle.coe_eq_one.1 hw, map_one]

/-- **The subgroup fixing the canonical eigenspace is the unitary group**: the rotation
homomorphism `Spinᶜ(4) → SO(4)` restricts to an isomorphism from the subgroup fixing the canonical
eigenspace onto the rotations commuting with `J`. -/
def canonicalLineFixingSubgroupEquiv :
    canonicalLineFixingSubgroup o ρ J hQ₀ ≃* J.unitaryGroup Q :=
  MulEquiv.ofBijective (((spinCGroup.toSpecialOrthogonal Q hQ₀).comp
      (canonicalLineFixingSubgroup o ρ J hQ₀).subtype).codRestrict (J.unitaryGroup Q)
        fun x ↦ toSpecialOrthogonal_mem_unitaryGroup_of_mem_canonicalLineFixingSubgroup
          hQ hJ ho hQ₀ x.property) <| by
    refine ⟨(injective_iff_map_eq_one _).2 fun x hx ↦ Subtype.ext ?_, fun A ↦ ?_⟩
    · exact eq_one_of_mem_canonicalLineFixingSubgroup_of_toSpecialOrthogonal_eq_one hQ hJ ho
        hQ₀ x.property (congrArg Subtype.val hx)
    · obtain ⟨x, hx, hxA⟩ :=
        exists_mem_canonicalLineFixingSubgroup_toSpecialOrthogonal_eq_of_mem_unitaryGroup
          (ρ := ρ) hQ hJ hQ₀ A.property
      exact ⟨⟨x, hx⟩, Subtype.ext hxA⟩

/-- The isomorphism `canonicalLineFixingSubgroupEquiv` is the rotation homomorphism. -/
@[simp]
theorem coe_canonicalLineFixingSubgroupEquiv_apply
    (x : canonicalLineFixingSubgroup o ρ J hQ₀) :
    (canonicalLineFixingSubgroupEquiv hQ hJ ho hQ₀ x :
      TauCeti.QuadraticMap.specialOrthogonalGroup Q) = spinCGroup.toSpecialOrthogonal Q hQ₀ x :=
  (rfl)

variable (ρ) in
/-- **The canonical `Spinᶜ` lift of the unitary group** `U(V, J) → Spinᶜ(4)`: the inverse of the
rotation homomorphism on the subgroup fixing the canonical eigenspace. It lifts the inclusion
`U(V, J) ⊆ SO(4)` (`toSpecialOrthogonal_unitaryLift`) and is characterized among such lifts by
acting trivially on the canonical eigenspace (`eq_unitaryLift_iff`); its determinant character is
the scalar by which it acts on the complementary eigenspace
(`spinCGroupHalfSpinRep_apply_eq_det_smul_of_mem_canonicalLineFixingSubgroup_of_bivectorExterior`).
-/
def unitaryLift : J.unitaryGroup Q →* spinCGroup Q hQ₀ :=
  (canonicalLineFixingSubgroup o ρ J hQ₀).subtype.comp
    (canonicalLineFixingSubgroupEquiv (ρ := ρ) hQ hJ ho hQ₀).symm.toMonoidHom

/-- The canonical lift fixes the canonical eigenspace. -/
@[simp]
theorem unitaryLift_mem_canonicalLineFixingSubgroup (A : J.unitaryGroup Q) :
    unitaryLift ρ hQ hJ ho hQ₀ A ∈ canonicalLineFixingSubgroup o ρ J hQ₀ :=
  ((canonicalLineFixingSubgroupEquiv (ρ := ρ) hQ hJ ho hQ₀).symm A).property

/-- **The canonical lift lifts the inclusion `U(V, J) ⊆ SO(4)`**: the rotation of
`unitaryLift A` is `A`. -/
@[simp]
theorem toSpecialOrthogonal_unitaryLift (A : J.unitaryGroup Q) :
    spinCGroup.toSpecialOrthogonal Q hQ₀ (unitaryLift ρ hQ hJ ho hQ₀ A) = A :=
  congrArg Subtype.val
    ((canonicalLineFixingSubgroupEquiv (ρ := ρ) hQ hJ ho hQ₀).apply_symm_apply A)

/-- **Characterization of the canonical lift**: `x` is the canonical lift of `A` exactly when it
fixes the canonical eigenspace and has rotation `A`. -/
theorem eq_unitaryLift_iff {x : spinCGroup Q hQ₀} {A : J.unitaryGroup Q} :
    x = unitaryLift ρ hQ hJ ho hQ₀ A ↔
      x ∈ canonicalLineFixingSubgroup o ρ J hQ₀ ∧ spinCGroup.toSpecialOrthogonal Q hQ₀ x = A := by
  refine ⟨fun h ↦ h ▸ ⟨unitaryLift_mem_canonicalLineFixingSubgroup hQ hJ ho hQ₀ A,
    toSpecialOrthogonal_unitaryLift hQ hJ ho hQ₀ A⟩, fun ⟨hx, hxA⟩ ↦ ?_⟩
  have h := (canonicalLineFixingSubgroupEquiv (ρ := ρ) hQ hJ ho hQ₀).symm_apply_apply ⟨x, hx⟩
  have hA : canonicalLineFixingSubgroupEquiv (ρ := ρ) hQ hJ ho hQ₀ ⟨x, hx⟩ = A :=
    Subtype.ext hxA
  rw [hA] at h
  exact (congrArg Subtype.val h).symm

/-- An element fixing the canonical eigenspace is the canonical lift of its rotation. -/
@[simp]
theorem unitaryLift_toSpecialOrthogonal_of_mem_canonicalLineFixingSubgroup {x : spinCGroup Q hQ₀}
    (hx : x ∈ canonicalLineFixingSubgroup o ρ J hQ₀) :
    unitaryLift ρ hQ hJ ho hQ₀
        ⟨spinCGroup.toSpecialOrthogonal Q hQ₀ x,
          toSpecialOrthogonal_mem_unitaryGroup_of_mem_canonicalLineFixingSubgroup
            hQ hJ ho hQ₀ hx⟩ = x :=
  ((eq_unitaryLift_iff hQ hJ ho hQ₀).2 ⟨hx, rfl⟩).symm

/-- **The canonical lift acts on the negative half-spinors as `A` acts on `V`.** For `u` in the
canonical eigenspace, the map `v ↦ c(v) u` from `V` to the negative half-spinors intertwines `A`
with the action of its canonical lift. -/
theorem spinCGroupHalfSpinRep_unitaryLift_halfSpinCliffordMul
    {u : eigenspace (ρ (chirality Q o)) 1}
    (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • (u : W))
    (A : J.unitaryGroup Q) (v : V) :
    spinCGroupHalfSpinRep o ρ (-1) hQ₀ (unitaryLift ρ hQ hJ ho hQ₀ A)
        (halfSpinCliffordMul o ρ 1 v u) =
      halfSpinCliffordMul o ρ 1
        (((A : TauCeti.QuadraticMap.specialOrthogonalGroup Q) : V ≃ₗ[ℝ] V) v) u := by
  have hxu := unitaryLift_mem_canonicalLineFixingSubgroup (ρ := ρ) hQ hJ ho hQ₀ A u hu
  have h := ι_apply_spinCGroupHalfSpinRep_apply o ρ 1 hQ₀ (unitaryLift ρ hQ hJ ho hQ₀ A) v u
  rw [hxu, toSpecialOrthogonal_unitaryLift] at h
  exact Subtype.ext (by simpa using h.symm)

/-- **The canonical lift on products `c(v) c(w) u`**: for `u` in the canonical eigenspace, the
canonical lift of `A` sends the positive half-spinor `c(v) c(w) u` to `c(A v) c(A w) u`. -/
theorem coe_spinCGroupHalfSpinRep_unitaryLift_apply_of_coe_eq
    {u : eigenspace (ρ (chirality Q o)) 1}
    (hu : ρ (bivectorExterior Q J.kahlerForm) u = (-2 * Complex.I) • (u : W))
    (A : J.unitaryGroup Q) {v w : V} {φ : eigenspace (ρ (chirality Q o)) 1}
    (hφ : (φ : W) = ρ (ι Q v) (ρ (ι Q w) u)) :
    (spinCGroupHalfSpinRep o ρ 1 hQ₀ (unitaryLift ρ hQ hJ ho hQ₀ A) φ : W) =
      ρ (ι Q (((A : TauCeti.QuadraticMap.specialOrthogonalGroup Q) : V ≃ₗ[ℝ] V) v))
        (ρ (ι Q (((A : TauCeti.QuadraticMap.specialOrthogonalGroup Q) : V ≃ₗ[ℝ] V) w)) u) := by
  have h := ι_apply_spinCGroupHalfSpinRep_apply o ρ (-1) hQ₀
    (unitaryLift ρ hQ hJ ho hQ₀ A) v (halfSpinCliffordMul o ρ 1 w u)
  rw [toSpecialOrthogonal_unitaryLift,
    spinCGroupHalfSpinRep_unitaryLift_halfSpinCliffordMul hQ hJ ho hQ₀ hu A,
    coe_halfSpinCliffordMul_apply_apply] at h
  rw [h]
  exact coe_spinCGroupHalfSpinRep_apply_congr _ (neg_neg 1).symm (by simp [hφ])

end Lift

/-! ### The frame model, complex determinant, and circle lift -/

section FrameModel

open scoped _root_.Matrix
open AlmostComplexStructure (unitaryGroupFrameEquiv complexCoords_unitaryGroupFrameEquiv_apply)

variable [Nontrivial W] {J : AlmostComplexStructure V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)

/-- **The frame model of the canonical lift.** The canonical lift of `unitaryGroupFrameEquiv g`
is `e.spinCUnitary g`: in the complex coordinates of any unitary frame `e`, `unitaryLift` agrees
with the quaternionic lift `OrthonormalBasis.spinCUnitary` of `U(2)`, which needs no spin module.
-/
theorem unitaryLift_unitaryGroupFrameEquiv {e : OrthonormalBasis (Fin 4) ℝ V}
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (ho : J.orientation Fact.out = o) (hQ₀ : Q ≠ 0)
    (g : Matrix.unitaryGroup (Fin 2) ℂ) :
    unitaryLift ρ hQ (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂) ho hQ₀
        (unitaryGroupFrameEquiv hQ h₀ h₂ g) =
      e.spinCUnitary hQ hQ₀ g :=
  ((eq_unitaryLift_iff (ρ := ρ) hQ _ ho hQ₀).2
    ⟨spinCUnitary_mem_canonicalLineFixingSubgroup hQ h₀ h₂ hQ₀ g,
      toSpecialOrthogonal_spinCUnitary_eq_unitaryGroupFrameEquiv hQ h₀ h₂ hQ₀ g⟩).symm

/-- **The canonical lift in a unitary frame.** The canonical lift of a rotation `A` in `U(V, J)` is
the frame model `e.spinCUnitary` of its matrix `(unitaryGroupFrameEquiv).symm A` in the complex
coordinates of `e`. -/
theorem unitaryLift_eq_spinCUnitary {e : OrthonormalBasis (Fin 4) ℝ V}
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (ho : J.orientation Fact.out = o) (hQ₀ : Q ≠ 0)
    (A : J.unitaryGroup Q) :
    unitaryLift ρ hQ (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂) ho hQ₀ A =
      e.spinCUnitary hQ hQ₀ ((unitaryGroupFrameEquiv hQ h₀ h₂).symm A) := by
  rw [← unitaryLift_unitaryGroupFrameEquiv (ρ := ρ) hQ h₀ h₂ ho hQ₀, MulEquiv.apply_symm_apply]

/-- **The canonical lift restricts to `spinCCircle` on the complex line `⟨e₂, e₃⟩`**: the
canonical lift of the rotation of `⟨e₂, e₃⟩` by `z` is `spinCCircle z`, the `Spinᶜ` lift of the
rotations of that oriented plane. -/
theorem unitaryLift_toSpecialOrthogonal_spinCCircle {e : OrthonormalBasis (Fin 4) ℝ V}
    (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (ho : J.orientation Fact.out = o) (hQ₀ : Q ≠ 0)
    (z : Circle) :
    unitaryLift ρ hQ (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂) ho hQ₀
        ⟨spinCGroup.toSpecialOrthogonal Q hQ₀ (spinCCircle Q hQ₀ (e 2) (e 3)
            (e.isOrtho_apply hQ (by decide)) (e.map_apply_mul_map_apply hQ 2 3) z),
          toSpecialOrthogonal_mem_unitaryGroup_of_mem_canonicalLineFixingSubgroup
            hQ (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂) ho hQ₀
            (spinCCircle_mem_canonicalLineFixingSubgroup (ρ := ρ) hQ h₀ h₂ hQ₀ z)⟩ =
      spinCCircle Q hQ₀ (e 2) (e 3) (e.isOrtho_apply hQ (by decide))
        (e.map_apply_mul_map_apply hQ 2 3) z :=
  unitaryLift_toSpecialOrthogonal_of_mem_canonicalLineFixingSubgroup (ρ := ρ)
    hQ (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂) ho hQ₀
    (spinCCircle_mem_canonicalLineFixingSubgroup hQ h₀ h₂ hQ₀ z)

/-- **The determinant character of the canonical lift is the complex determinant.** The canonical
`Spinᶜ` lift of a unitary rotation `A` of `(V, J)` has determinant character `det_ℂ A`, the
determinant of `A` as a `ℂ`-linear map of the complex vector space `(V, J)`. At the level of
structure groups, this says that the determinant line of the canonical `Spinᶜ` structure of an
almost Hermitian four-manifold is the anticanonical line `K⁻¹ = Λ²_ℂ (T X, J)`. -/
theorem det_unitaryLift (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (ho : J.orientation Fact.out = o)
    (hQ₀ : Q ≠ 0) (A : J.unitaryGroup Q) :
    letI := J.complexModule
    (spinCGroup.det Q hQ₀ (unitaryLift ρ hQ hJ ho hQ₀ A) : ℂ) =
      LinearMap.det
        (AlmostComplexStructure.isComplexLinearMap_of_mem_unitaryGroup
            A.property).toComplexLinearMap := by
  obtain ⟨e, h₀, h₂⟩ := AlmostComplexStructure.exists_unitary_orthonormalBasis hJ
  let := J.complexModule
  have := J.complexModule_isScalarTower
  set g := (unitaryGroupFrameEquiv hQ h₀ h₂).symm A
  let C := (AlmostComplexStructure.basisOfOrthonormalBasisFinFour h₀ h₂).equivFun
  rw [unitaryLift_eq_spinCUnitary (ρ := ρ) hQ h₀ h₂ ho hQ₀ A, e.det_spinCUnitary hQ hQ₀,
    Matrix.UnitaryGroup.coe_detCircle, ← LinearMap.det_toLin', ← LinearMap.det_conj _ C.symm]
  congr 1
  refine LinearMap.ext fun v ↦ C.injective ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply, IsComplexLinearMap.toComplexLinearMap_apply,
    Matrix.toLin'_apply]
  rw [AlmostComplexStructure.basisOfOrthonormalBasisFinFour_equivFun_apply,
    AlmostComplexStructure.basisOfOrthonormalBasisFinFour_equivFun_apply]
  have hAg : (unitaryGroupFrameEquiv hQ h₀ h₂ g :
      TauCeti.QuadraticMap.specialOrthogonalGroup Q) = A :=
    congrArg Subtype.val ((unitaryGroupFrameEquiv hQ h₀ h₂).apply_symm_apply A)
  rw [← hAg]
  exact (complexCoords_unitaryGroupFrameEquiv_apply hQ h₀ h₂ g v).symm

end FrameModel

/-! ### Continuity of the canonical lift -/

section Continuity

variable [Nontrivial W] {J : AlmostComplexStructure V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
  (ho : J.orientation Fact.out = o) (hQ₀ : Q ≠ 0)

/-- **The subgroup fixing the canonical eigenspace is the unitary group, as a topological group**:
the rotation homomorphism, as an isomorphism of topological groups from the subgroup of `Spinᶜ(4)`
fixing the canonical eigenspace onto `U(V, J)`. Its underlying group isomorphism is
`canonicalLineFixingSubgroupEquiv`. -/
def canonicalLineFixingSubgroupContinuousMulEquiv :
    canonicalLineFixingSubgroup o ρ J hQ₀ ≃ₜ* J.unitaryGroup Q :=
  have hneg : (-Q).PosDef := fun v hv ↦ by simpa [hQ] using pow_pos (norm_pos_iff.2 hv) 2
  have : CompactSpace (spinCGroup Q hQ₀) :=
    spinCGroup.compactSpace_of_posDef_or_negDef Q hQ₀ (Or.inr hneg)
  have : CompactSpace (canonicalLineFixingSubgroup o ρ J hQ₀) :=
    isCompact_iff_compactSpace.mp
      (isClosed_canonicalLineFixingSubgroup o ρ J hQ₀).isCompact
  have hc : Continuous (canonicalLineFixingSubgroupEquiv (ρ := ρ) hQ hJ ho hQ₀) :=
    (((spinCGroup.continuous_toSpecialOrthogonal Q hQ₀).comp continuous_subtypeVal).subtype_mk _)
  { canonicalLineFixingSubgroupEquiv (ρ := ρ) hQ hJ ho hQ₀ with
    continuous_toFun := hc
    continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2
      (f := (canonicalLineFixingSubgroupEquiv (ρ := ρ) hQ hJ ho hQ₀).toEquiv) }

/-- The continuous isomorphism `canonicalLineFixingSubgroupContinuousMulEquiv` is the rotation
homomorphism, as `canonicalLineFixingSubgroupEquiv` is. -/
@[simp]
theorem canonicalLineFixingSubgroupContinuousMulEquiv_apply
    (x : canonicalLineFixingSubgroup o ρ J hQ₀) :
    canonicalLineFixingSubgroupContinuousMulEquiv hQ hJ ho hQ₀ x =
      canonicalLineFixingSubgroupEquiv hQ hJ ho hQ₀ x :=
  (rfl)

/-- The inverse of `canonicalLineFixingSubgroupContinuousMulEquiv` is the inverse of
`canonicalLineFixingSubgroupEquiv`. -/
@[simp]
theorem canonicalLineFixingSubgroupContinuousMulEquiv_symm_apply (A : J.unitaryGroup Q) :
    (canonicalLineFixingSubgroupContinuousMulEquiv (ρ := ρ) hQ hJ ho hQ₀).symm A =
      (canonicalLineFixingSubgroupEquiv (ρ := ρ) hQ hJ ho hQ₀).symm A :=
  (rfl)

/-- **The canonical lift is continuous**: `U(V, J) → Spinᶜ(4)` is the inverse of the continuous
isomorphism `canonicalLineFixingSubgroupContinuousMulEquiv`, followed by the inclusion. -/
@[fun_prop]
theorem continuous_unitaryLift : Continuous (unitaryLift ρ hQ hJ ho hQ₀) :=
  continuous_subtypeVal.comp
    (canonicalLineFixingSubgroupContinuousMulEquiv (ρ := ρ) hQ hJ ho hQ₀).symm.continuous

variable (ρ) in
/-- **The canonical `Spinᶜ` lift of the unitary group, as a continuous homomorphism**
`U(V, J) →ₜ* Spinᶜ(4)`. Continuity is what extending a principal bundle along this structure
group homomorphism requires. -/
def unitaryLiftContinuousMonoidHom : J.unitaryGroup Q →ₜ* spinCGroup Q hQ₀ where
  toMonoidHom := unitaryLift ρ hQ hJ ho hQ₀
  continuous_toFun := continuous_unitaryLift hQ hJ ho hQ₀

/-- The bundled continuous canonical lift is the canonical lift. -/
@[simp]
theorem unitaryLiftContinuousMonoidHom_apply (A : J.unitaryGroup Q) :
    unitaryLiftContinuousMonoidHom ρ hQ hJ ho hQ₀ A = unitaryLift ρ hQ hJ ho hQ₀ A :=
  (rfl)

end Continuity

end TauCeti.SeibergWitten

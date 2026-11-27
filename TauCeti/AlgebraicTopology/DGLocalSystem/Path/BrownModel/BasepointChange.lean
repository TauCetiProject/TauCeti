/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Augmentation
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.QuasiIso
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Bimodule
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BrownModel.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.CoefficientPairing

/-!
# Changing the basepoint of a Brown model

Let `M` be a Brown model at a point `b` of a space `B` (`TauCeti.BrownModel`): a semi-free
row-finite twisting cocycle `m` over the chains `C_*(Ω_b B)` on the Moore loops at `b`, on
generators `P`, with a quasi-isomorphism `g : K_m → C_*(P_b B)` of left modules onto the chains on
the Moore paths starting at `b`. For another point `a`, the chains `C_*(P_{a→b} B)` on the Moore
paths from `a` to `b` are a `(C_*(Ω_a B), C_*(Ω_b B))`-bimodule (`TauCeti.pathChain_isDGBimodule`),
the bimodule along which DG local systems change their basepoint. So the twisted complex of `m`
with coefficients in `C_*(P_{a→b} B)`, on the finitely supported vectors `P →₀ C_*(P_{a→b} B)`, is
the change of basepoint of `K_m` from `b` to `a`.

Concatenating a path from `a` to `b` with a path from `b`
(`TauCeti.MoorePathBetween.transFrom`) gives the **basepoint-change comparison**
(`TauCeti.BrownModel.basepointChangeComparison`)

`C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} K_m → C_*(P_a B)`,  `σ ⊗ x ↦ σ ⋆ g(x)`,

a map onto the chains on the Moore paths starting at `a`. It commutes with the differentials
(`TauCeti.BrownModel.basepointChangeComparison_coefficientDifferential`): the twisting equation of
`m` corresponds through `g` to the boundaries of the chains `g(x)`, concatenation is balanced over
the loops at `b`, and the boundary is a derivation for it. It is linear over the chains on the
loops at `a` acting in front (`TauCeti.BrownModel.basepointChangeComparison_smul`). When `a` and `b`
are joined by a path, it is a quasi-isomorphism
(`TauCeti.BrownModel.exists_coefficientDifferential_eq_and_basepointChangeComparison_add_eq`),
stated on elements as for Brown models: every relative cycle is a relative boundary. So the change
of basepoint of Brown's model at `b` is a model at `a` of the chains on the based path space, over
the chains on the loops at `a`; it is not semi-free over them.

For the proof choose a Moore path `γ` from `a` to `b`. Prepending `γ` is a quasi-isomorphism
`C_*(Ω_b B) → C_*(P_{a→b} B)` of right modules (`TauCeti.isQuasiIso_loopChainPrepend`), and since
`m` is semi-free it induces a quasi-isomorphism of twisted complexes
(`TauCeti.RowFiniteTwistingCocycle.exists_coefficientDifferential_eq_of_forall_exists`). With
coefficients in the loop chains themselves the twisted complex is `K_m`
(`TauCeti.RowFiniteTwistingCocycle.mapRange_cubicalChainModuleEquiv_coefficientDifferential`), and
on it the comparison is `g` followed by prepending `γ` to paths from `b`, a map between contractible
spaces. Both are quasi-isomorphisms, hence so is their composite
(`TauCeti.exists_differential_eq_and_comp_add_eq`), and the comparison is one by two out of three
(`TauCeti.exists_differential_eq_and_add_eq_of_comp`).

The quasi-isomorphism statement takes the space and the coefficient ring in one universe, as the
homotopy invariance of cubical chains behind `TauCeti.isQuasiIso_loopChainPrepend` does.

## Main definitions

* `TauCeti.BrownModel.basepointChangeComparison M a`: the map
  `C_*(P_{a→b} B) ⊗ K_m → C_*(P_a B)`, `σ ⊗ x ↦ σ ⋆ g(x)`.

## Main results

* `TauCeti.RowFiniteTwistingCocycle.mapRange_cubicalChainModuleEquiv_coefficientDifferential`:
  with coefficients in the chains of a topological monoid, a right module over themselves, the
  twisted complex of a cocycle over these chains is its free module.
* `TauCeti.BrownModel.basepointChangeComparison_coefficientDifferential`: the comparison commutes
  with the differentials.
* `TauCeti.BrownModel.basepointChangeComparison_smul`: it is linear over `C_*(Ω_a B)`.
* `TauCeti.BrownModel.exists_coefficientDifferential_eq_and_basepointChangeComparison_add_eq`: it
  is a quasi-isomorphism when `a` and `b` are joined by a path.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2, §6.4 and §7.1.
-/

public section

noncomputable section

universe u

namespace TauCeti

/-! ### Coefficients in the chains of the loops -/

section Regular

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G] {R : Type*} [CommRing R]
  {P : Type*} {ind : P → ℤ}

/-- With coefficients in the chains of `G`, a right module over themselves, the twisted complex of
a row-finite cocycle over the chains of `G` is the free module `K_m`: read through
`TauCeti.cubicalChainModuleEquiv`, the two differentials agree. -/
theorem RowFiniteTwistingCocycle.mapRange_cubicalChainModuleEquiv_coefficientDifferential
    (m : RowFiniteTwistingCocycle (R := R) (A := normalizedCubicalChainAlgebra G R)
      (cubicalChainGrading G R) (cubicalChainDifferential G R) P ind)
    (f : P →₀ cubicalChainModule G G R) :
    Finsupp.mapRange.linearMap (cubicalChainModuleEquiv G G R).toLinearMap
        (m.coefficientDifferential (cubicalChainModule_isDGRightModule G G R) f) =
      rowFiniteTwistedDifferential (R := R) (A := normalizedCubicalChainAlgebra G R)
        (𝒜 := cubicalChainGrading G R) (d := cubicalChainDifferential G R) m.m
        (Finsupp.mapRange.linearMap (cubicalChainModuleEquiv G G R).toLinearMap f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [map_add, hf, hf']
  | single x α =>
    induction α using DirectSum.Decomposition.inductionOn (cubicalChainModuleGrading G G R) with
    | zero => simp
    | add α α' hα hα' => simp only [Finsupp.single_add, map_add, hα, hα']
    | @homogeneous q α =>
      have hα : cubicalChainModuleEquiv G G R α ∈ cubicalChainGrading G R q :=
        mem_cubicalChainModuleGrading.1 α.property
      rw [m.coefficientDifferential_single _ x α.property, map_add, Units.smul_def, map_zsmul,
        map_finsuppSum]
      simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, LinearEquiv.coe_coe]
      rw [rowFiniteTwistedDifferential_single (R := R) (A := normalizedCubicalChainAlgebra G R)
        (𝒜 := cubicalChainGrading G R) (d := cubicalChainDifferential G R) m.m x hα,
        Units.smul_def]
      simp only [cubicalChainModuleEquiv_differential, cubicalChainModuleEquiv_op_smul_self]
      congr 2
      conv_rhs => rw [← Finsupp.sum_single (m.m x)]
      rw [Finsupp.smul_sum]
      simp [Finsupp.smul_single]

end Regular

/-! ### The comparison map -/

namespace BrownModel

variable {B : Type*} [TopologicalSpace B] {b : B} {H : Type*} {R : Type*} [CommRing R]
  {P : Type*} {ind : P → ℤ}

/-- The **basepoint-change comparison** of a Brown model `M` at `b`, for a point `a`: the map
`C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} K_m → C_*(P_a B)`, `σ ⊗ x ↦ σ ⋆ g(x)`, from the twisted complex of
the cocycle of `M` with coefficients in the chains on the Moore paths from `a` to `b`, written on
finitely supported coefficient vectors, to the chains on the Moore paths starting at `a`. A
coefficient `σ` at the generator `x` goes to the concatenation of `σ` with the image `g(x)` of `x`
in the chains on the paths from `b`. -/
def basepointChangeComparison (M : BrownModel B b H R P ind) (a : B) :
    (P →₀ cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) →ₗ[R]
      cubicalChainModule (MoorePathFrom B a) H R :=
  coefficientPairing M.comparison (MoorePathBetween.transFrom a b)

/-- The comparison of a coefficient `σ` at a single generator `x` is the concatenation of `σ` with
the image of `x`. -/
@[simp]
theorem basepointChangeComparison_single (M : BrownModel B b H R P ind) (a : B) (x : P)
    (σ : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    M.basepointChangeComparison a (Finsupp.single x σ) =
      cubicalChainPairing (MooreLoopSpace B b) H R (MoorePathBetween.transFrom a b) σ
        (M.comparison x) :=
  coefficientPairing_single _ _ x σ

/-- **The basepoint-change comparison commutes with the differentials**: it sends the twisted
differential, with coefficients in `C_*(P_{a→b} B)`, to the boundary of chains on the paths from
`a`. -/
theorem basepointChangeComparison_coefficientDifferential (M : BrownModel B b H R P ind) (a : B)
    (f : P →₀ cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    M.basepointChangeComparison a (M.cocycle.coefficientDifferential
        (cubicalChainModule_isDGRightModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) f) =
      cubicalChainModuleDifferential (MoorePathFrom B a) H R (M.basepointChangeComparison a f) :=
  coefficientPairing_coefficientDifferential M.cocycle M.linearCombination_comparison_m
    (fun ω γ δ ↦ MoorePathBetween.transFrom_op_smul ω γ δ) f

/-- **The basepoint-change comparison is linear over the chains on the loops at `a`**, acting on the
coefficients in front and on the chains on the paths from `a` by concatenation in front. -/
theorem basepointChangeComparison_smul (M : BrownModel B b H R P ind) (a : B)
    (c : loopChainAlgebra B a R)
    (f : P →₀ cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    M.basepointChangeComparison a (c • f) = c • M.basepointChangeComparison a f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [smul_add, map_add, hf, hf']
  | single x σ =>
    rw [Finsupp.smul_single, basepointChangeComparison_single, basepointChangeComparison_single,
      cubicalChainPairing_smul_left _ (fun ω γ δ ↦ MoorePathBetween.transFrom_smul ω γ δ)]

/-- Prepending a Moore path `γ` from `a` to `b` to the paths from `b`. -/
private abbrev prependFrom {a : B} (γ : MoorePathBetween B a b) :
    C(MoorePathFrom B b, MoorePathFrom B a) :=
  (MoorePathBetween.transFrom a b).comp ((ContinuousMap.const _ γ).prodMk (ContinuousMap.id _))

/-- On coefficients in the loop chains, mapped into the path chains by prepending `γ`, the
comparison is the comparison of `M` followed by prepending `γ`. -/
private theorem basepointChangeComparison_mapRange_loopChainPrepend
    (M : BrownModel B b H R P ind) {a : B} (γ : MoorePathBetween B a b)
    (f : P →₀ cubicalChainModule (MooreLoopSpace B b) (MooreLoopSpace B b) R) :
    M.basepointChangeComparison a
        (Finsupp.mapRange.linearMap ((loopChainPrepend R γ).toLinearMap.restrictScalars R) f) =
      cubicalChainModuleLinearMap R (prependFrom γ)
        (Finsupp.linearCombination (loopChainAlgebra B b R) M.comparison
          (Finsupp.mapRange.linearMap (cubicalChainModuleEquiv (MooreLoopSpace B b)
            (MooreLoopSpace B b) R).toLinearMap f)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [map_add, hf, hf']
  | single x α =>
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, basepointChangeComparison_single,
      Finsupp.linearCombination_single]
    rw [DGRightModuleHom.coe_toLinearMap, loopChainPrepend_apply,
      cubicalChainPairing_cubicalChainModuleLinearMap_left,
      cubicalChainModuleEquiv_smul_eq_cubicalChainPairing,
      cubicalChainModuleLinearMap_cubicalChainPairing]
    -- Both maps send `(ω, δ)` to `γ ⋆ ω ⋆ δ`.
    have h : (MoorePathBetween.transFrom a b).comp
        (γ.loopPrependHomotopyEquiv.toFun.prodMap (ContinuousMap.id (MoorePathFrom B b))) =
          (prependFrom γ).comp (leftActMap (MooreLoopSpace B b) (MoorePathFrom B b)) :=
      ContinuousMap.ext fun p ↦ MoorePathFrom.ext (by simp [MoorePath.trans_assoc])
    rw [h]

/-- **The basepoint-change comparison of a Brown model is a quasi-isomorphism.** Let `M` be a Brown
model at `b` and `a` a point joined to `b` by a Moore path. Then every relative cycle `(u, w)` of
the comparison `C_*(P_{a→b} B) ⊗ K_m → C_*(P_a B)`, with `D u = 0` and `Θ u = ∂ w`, is a relative
boundary `(D u', Θ u' + ∂ w')`. So tensoring Brown's model at `b` with the path bimodule, which
changes its basepoint to `a`, gives a model at `a` of the chains on the based path space. -/
theorem exists_coefficientDifferential_eq_and_basepointChangeComparison_add_eq
    {B : Type u} [TopologicalSpace B] {b : B} {R : Type u} [CommRing R]
    (M : BrownModel B b H R P ind) {a : B} (hab : Nonempty (MoorePathBetween B a b))
    (u : P →₀ cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (w : cubicalChainModule (MoorePathFrom B a) H R)
    (hu : M.cocycle.coefficientDifferential
      (cubicalChainModule_isDGRightModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) u = 0)
    (hw : M.basepointChangeComparison a u =
      cubicalChainModuleDifferential (MoorePathFrom B a) H R w) :
    ∃ u' w', M.cocycle.coefficientDifferential
        (cubicalChainModule_isDGRightModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) u' =
          u ∧
      M.basepointChangeComparison a u' + cubicalChainModuleDifferential (MoorePathFrom B a) H R w' =
        w := by
  obtain ⟨γ⟩ := hab
  set e := cubicalChainModuleEquiv (MooreLoopSpace B b) (MooreLoopSpace B b) R
  set E := Finsupp.mapRange.linearMap (α := P) e.toLinearMap
  set E' := Finsupp.mapRange.linearMap (α := P) e.symm.toLinearMap
  have hE (v : P →₀ loopChainAlgebra B b R) : E (E' v) = v :=
    Finsupp.ext fun x ↦ by simp [E, E']
  have hEinj : Function.Injective E :=
    Finsupp.mapRange_injective _ (map_zero e) e.injective
  -- Factor through the twisted complex with coefficients in the loop chains, mapped into the
  -- path chains by prepending `γ`, a quasi-isomorphism of DG right modules.
  refine exists_differential_eq_and_add_eq_of_comp
    (g := Finsupp.mapRange.linearMap ((loopChainPrepend R γ).toLinearMap.restrictScalars R))
    (fun v ↦ (M.cocycle.coefficientDifferential_mapRange _ _ (loopChainPrepend R γ) v).symm)
    (M.basepointChangeComparison_coefficientDifferential a)
    (fun v y hv hvy ↦ M.cocycle.exists_coefficientDifferential_eq_of_forall_exists _ _
      M.wellFounded (loopChainPrepend R γ)
      ((DGRightModuleHom.isQuasiIso_iff_forall_exists _).1 (isQuasiIso_loopChainPrepend R γ))
      hv hvy)
    (fun v y hv hvy ↦ ?_) u w hu hw
  -- On these coefficients the comparison is that of `M`, a quasi-isomorphism, followed by
  -- prepending `γ`, a map between contractible spaces.
  rw [basepointChangeComparison_mapRange_loopChainPrepend] at hvy
  obtain ⟨v', y', hv', hy'⟩ := exists_differential_eq_and_comp_add_eq
    (g := (Finsupp.linearCombination (loopChainAlgebra B b R) M.comparison).restrictScalars R)
    M.linearCombination_differential
    (fun c ↦ (cubicalChainModuleDifferential_linearMap _ c).symm)
    M.exists_differential_eq_and_linearCombination_add_eq
    (fun c z hc hcz ↦ exists_differential_eq_and_add_eq_of_augmentation
      (fun x ↦ (cubicalChainModuleDifferential_linearMap _ x).symm)
      (cubicalChainModuleAugmentation_linearMap _) cubicalChainModuleAugmentation_differential
      (cubicalChainModuleDifferential_cubicalChainModulePoint (MoorePathFrom.refl B b))
      (cubicalChainModuleAugmentation_cubicalChainModulePoint _)
      exists_pathFromChainDifferential_eq_of_augmentation_eq_zero
      exists_pathFromChainDifferential_eq_of_augmentation_eq_zero hc hcz)
    (E v) y (by
      rw [← RowFiniteTwistingCocycle.mapRange_cubicalChainModuleEquiv_coefficientDifferential, hv,
        map_zero]) hvy
  refine ⟨E' v', y', hEinj ?_, ?_⟩
  · rw [RowFiniteTwistingCocycle.mapRange_cubicalChainModuleEquiv_coefficientDifferential, hE, hv']
  · rw [basepointChangeComparison_mapRange_loopChainPrepend, hE]
    exact hy'

end BrownModel

end TauCeti

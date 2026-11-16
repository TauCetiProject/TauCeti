/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Geometry.Symplectic.Hamiltonian.Elliptic
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Linear
public import TauCeti.Geometry.Symplectic.PolarCompatible
public import TauCeti.Geometry.Symplectic.WeightDecomposition

/-!
# Morse–Bott data of the components of the moment map of a compact linear symplectic action

Let a compact Lie group `G` act smoothly and linearly on a finite-dimensional real symplectic
vector space `(V, ω)` by linear symplectomorphisms, for instance the isotropy representation of a
compact group of symplectomorphisms at a fixed point. Its quadratic moment map
(`TauCeti.SymplecticForm.linearActionMomentMap`) has the components

`μ^ξ(v) = ½ ω(ξ_V v, v)`,

where `ξ_V ∈ sp(V, ω)` is the linear fundamental vector field of `ξ`. This file proves that every
component is a Morse–Bott function with even index and even coindex:

* the Hessian of `μ^ξ` at every point is the quadratic form `v ↦ ω(ξ_V v, v)`
  (`TauCeti.SymplecticForm.hessianQuadraticForm_linearActionMomentMap_apply`);
* its null space is the kernel of `ξ_V`, which is also the critical set of `μ^ξ`, so at each
  critical point the null space of the Hessian is the tangent space of the critical set
  (`TauCeti.SymplecticForm.radical_hessianQuadraticForm_linearActionMomentMap_apply`,
  `TauCeti.SymplecticForm.fderiv_linearActionMomentMap_apply_eq_zero_iff`);
* its Morse index and its coindex, the positive index of inertia of the Hessian, are even
  (`TauCeti.SymplecticForm.even_morseIndex_linearActionMomentMap_apply`,
  `TauCeti.SymplecticForm.even_sigPos_hessianQuadraticForm_linearActionMomentMap_apply`).

The evenness is linear algebra. Compactness of `G` gives a complex structure `J` compatible with
`ω` for which every element of `G` is complex linear
(`TauCeti.SymplecticForm.exists_compatible_forall_isComplexLinearMap`), and then every `ξ_V` is
complex linear too, as the derivative of complex-linear maps
(`TauCeti.SymplecticForm.exists_compatible_forall_isComplexLinearMap_fundamentalLinearMap`). An
element `A` of `sp(V, ω)` which is complex linear for a compatible `J` is diagonal in a Darboux
basis `(q₁, p₁, …, qₙ, pₙ)` with `pₖ = J qₖ`, rotating each plane `span(qₖ, pₖ)` with an angular
frequency `νₖ`. Its quadratic Hamiltonian `½ ω(A v, v)` is then the combination `∑ₖ νₖ Iₖ` of the
elliptic blocks `Iₖ = (xₖ² + yₖ²) / 2`
(`TauCeti.SymplecticForm.exists_isDarbouxBasis_hamiltonianEndEquiv_symm_eq_sum_smul_elliptic`), in
which every frequency contributes two squares of the same sign. So its indices of inertia are twice
the numbers of negative and of positive frequencies
(`TauCeti.SymplecticForm.even_sigNeg_hamiltonianEndEquiv_symm`,
`TauCeti.SymplecticForm.even_sigPos_hamiltonianEndEquiv_symm`).

The frequencies need not be distinct, and no diagonalization of the whole group is used; only the
single element `ξ_V` is put in normal form. Without compactness the conclusion fails: the
hyperbolic Hamiltonian `q p` on the plane is the component of the moment map of the linear action
of `ℝ` by `(q, p) ↦ (eᵗ q, e⁻ᵗ p)`, and has Morse index one.

By the equivariant Darboux theorem the isotropy representation is the local model of a compact
symplectic action near a fixed point, so these are the local Morse–Bott data of the components of
its moment map there.

## Main results

* `TauCeti.SymplecticForm.exists_isDarbouxBasis_hamiltonianEndEquiv_symm_eq_sum_smul_elliptic`: an
  element of `sp(V, ω)`, complex linear for a compatible complex structure, has quadratic
  Hamiltonian a combination of elliptic blocks in an adapted Darboux basis.
* `TauCeti.SymplecticForm.even_sigNeg_hamiltonianEndEquiv_symm`,
  `TauCeti.SymplecticForm.even_sigPos_hamiltonianEndEquiv_symm`: its indices of inertia are even.
* `TauCeti.SymplecticForm.exists_compatible_forall_isComplexLinearMap_fundamentalLinearMap`: for a
  compact group, every `ξ_V` is complex linear for one compatible complex structure.
* `TauCeti.SymplecticForm.hessianQuadraticForm_linearActionMomentMap_apply`: the Hessian of `μ^ξ`.
* `TauCeti.SymplecticForm.fderiv_linearActionMomentMap_apply_eq_zero_iff`: the critical set of
  `μ^ξ` is the kernel of `ξ_V`.
* `TauCeti.SymplecticForm.radical_hessianQuadraticForm_linearActionMomentMap_apply`: the null
  space of the Hessian is the kernel of `ξ_V`.
* `TauCeti.SymplecticForm.even_morseIndex_linearActionMomentMap_apply`,
  `TauCeti.SymplecticForm.even_sigPos_hessianQuadraticForm_linearActionMomentMap_apply`: for a
  compact group, the index and the coindex of `μ^ξ` are even.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15,
  § 2 (the components of the moment map are Morse–Bott with even indices).
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, Section 2.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 27.1.
-/

public section

noncomputable section

open Module
open scoped Manifold

namespace TauCeti.SymplecticForm

/-! ### Complex-linear elements of the symplectic Lie algebra -/

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- **Normal form of a compact element of `sp(V, ω)`.** Let `A ∈ sp(V, ω)` be complex linear for a
complex structure `J` compatible with `ω`. Then there are a Darboux basis `(q₁, p₁, …, qₙ, pₙ)`
with `pₖ = J qₖ` and real numbers `ν₁, …, νₙ` such that `A` rotates every plane `span(qₖ, pₖ)`
with angular frequency `νₖ`, `A qₖ = -νₖ pₖ` and `A pₖ = νₖ qₖ`, and its quadratic Hamiltonian
`v ↦ ½ ω(A v, v)` is `∑ₖ νₖ Iₖ`, for the elliptic blocks `Iₖ = (xₖ² + yₖ²) / 2` of the basis. -/
theorem exists_isDarbouxBasis_hamiltonianEndEquiv_symm_eq_sum_smul_elliptic
    (hJ : ω.Compatible J) (A : skewAdjointLieSubalgebra ω.toBilinForm)
    (hA : IsComplexLinearMap J J (A : Module.End ℝ V)) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (ν : Fin n → ℝ), ω.IsDarbouxBasis b ∧
      (∀ k, b (k, 1) = J (b (k, 0))) ∧
      (∀ k, (A : Module.End ℝ V) (b (k, 0)) = -ν k • b (k, 1) ∧
        (A : Module.End ℝ V) (b (k, 1)) = ν k • b (k, 0)) ∧
      ω.hamiltonianEndEquiv.symm A = ∑ k, ν k • elliptic b k := by
  obtain ⟨n, b, c, hb, hbJ, hc⟩ := exists_isDarbouxBasis_forall_apply_eq_of_skewAdjoint hJ
    (fun _ : Unit ↦ (A : Module.End ℝ V)) (fun _ _ h ↦ absurd rfl h) (fun _ ↦ A.2) fun _ ↦ hA
  -- `A` acts on `span(qₖ, pₖ)` by `a + b i`, and `ω(A qₖ, pₖ) = -ω(qₖ, A pₖ)` reads `a = -a`.
  have hre (k : Fin n) : (c () k).re = 0 := by
    have h : ω ((A : Module.End ℝ V) (b (k, 0))) (b (k, 1)) =
        -ω (b (k, 0)) ((A : Module.End ℝ V) (b (k, 1))) :=
      skewAdjointLieSubalgebra.apply_left A _ _
    rw [(hc () k).1, (hc () k).2] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hb.apply_fst_snd, hb.apply_snd_snd, hb.apply_fst_fst] at h
    simp at h
    linarith
  have hfst (k : Fin n) : (A : Module.End ℝ V) (b (k, 0)) = -(-(c () k).im) • b (k, 1) := by
    rw [(hc () k).1, hre, zero_smul, zero_add, neg_neg]
  have hsnd (k : Fin n) : (A : Module.End ℝ V) (b (k, 1)) = -(c () k).im • b (k, 0) := by
    rw [(hc () k).2, hre, zero_smul, add_zero]
  refine ⟨n, b, fun k ↦ -(c () k).im, hb, hbJ, fun k ↦ ⟨hfst k, hsnd k⟩,
    ω.hamiltonianEndEquiv.symm_apply_eq.2 (Subtype.ext (b.ext fun ⟨j, a⟩ ↦ ?_))⟩
  rw [coe_hamiltonianEndEquiv_apply]
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · rw [hfst, hb.hamiltonianEnd_sum_smul_elliptic_apply_fst]
  · rw [hsnd, hb.hamiltonianEnd_sum_smul_elliptic_apply_snd]

/-- **The negative index of a compact element of `sp(V, ω)` is even.** If `A ∈ sp(V, ω)` is complex
linear for a complex structure compatible with `ω`, the quadratic Hamiltonian `½ ω(A v, v)` has
even negative index of inertia. -/
theorem even_sigNeg_hamiltonianEndEquiv_symm (hJ : ω.Compatible J)
    (A : skewAdjointLieSubalgebra ω.toBilinForm)
    (hA : IsComplexLinearMap J J (A : Module.End ℝ V)) :
    Even (sigNeg (ω.hamiltonianEndEquiv.symm A)) := by
  obtain ⟨n, b, ν, -, -, -, h⟩ :=
    exists_isDarbouxBasis_hamiltonianEndEquiv_symm_eq_sum_smul_elliptic hJ A hA
  rw [h, sigNeg_sum_smul_elliptic]
  exact even_two_mul _

/-- **The positive index of a compact element of `sp(V, ω)` is even.** If `A ∈ sp(V, ω)` is complex
linear for a complex structure compatible with `ω`, the quadratic Hamiltonian `½ ω(A v, v)` has
even positive index of inertia. -/
theorem even_sigPos_hamiltonianEndEquiv_symm (hJ : ω.Compatible J)
    (A : skewAdjointLieSubalgebra ω.toBilinForm)
    (hA : IsComplexLinearMap J J (A : Module.End ℝ V)) :
    Even (sigPos (ω.hamiltonianEndEquiv.symm A)) := by
  obtain ⟨n, b, ν, -, -, -, h⟩ :=
    exists_isDarbouxBasis_hamiltonianEndEquiv_symm_eq_sum_smul_elliptic hJ A hA
  rw [h, sigPos_sum_smul_elliptic]
  exact even_two_mul _

end Algebraic

/-! ### Linear actions of Lie groups -/

attribute [local instance 100] LieRing.ofAssociativeRing

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [DistribMulAction G V] [SMulCommClass G ℝ V] [ContMDiffSMul I 𝓘(ℝ, V) 1 G V]
  {ω : SymplecticForm V}

/-- **Infinitesimal generators of complex-linear actions are complex linear.** If every element of
`G` acts on `V` complex linearly for a complex structure `J`, then so does every fundamental
vector field `ξ_V`, the derivative at the identity of the action. -/
theorem isComplexLinearMap_fundamentalLinearMap [FiniteDimensional ℝ V]
    {J : AlmostComplexStructure V}
    (hJ : ∀ (g : G) (v : V), J (g • v) = g • J v) (ξ : GroupLieAlgebra I G) :
    IsComplexLinearMap J J (fundamentalLinearMap I G V ξ) := by
  refine (isComplexLinearMap_iff_apply _ _ _).2 fun v ↦ ?_
  have hv := (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := 𝓘(ℝ, V)) (n := 1) v)
    |>.mdifferentiableAt one_ne_zero (x := (1 : G))
  -- The orbit map of `J v` is `J` composed with the orbit map of `v`.
  have horbit : (fun g : G ↦ g • J v) = LinearMap.toContinuousLinearMap J.toLinearMap ∘
      fun g : G ↦ g • v :=
    funext fun g ↦ (hJ g v).symm
  rw [fundamentalLinearMap_apply, fundamentalLinearMap_apply, horbit,
    ContinuousLinearMap.mvfderiv_comp_apply _ hv, LinearMap.coe_toContinuousLinearMap']

/-- **Compact linear symplectic actions have complex-linear generators.** For a linear action of a
compact Lie group `G` on `V` by linear symplectomorphisms of `ω`, there is a complex structure `J`
compatible with `ω` for which every fundamental vector field `ξ_V` is complex linear. -/
theorem exists_compatible_forall_isComplexLinearMap_fundamentalLinearMap [FiniteDimensional ℝ V]
    [IsTopologicalGroup G] [CompactSpace G] (hω : ∀ (g : G) (u w : V), ω (g • u) (g • w) = ω u w) :
    ∃ J : AlmostComplexStructure V, ω.Compatible J ∧
      ∀ ξ : GroupLieAlgebra I G, IsComplexLinearMap J J (fundamentalLinearMap I G V ξ) := by
  -- The action as a continuous representation of `G` by continuous linear maps.
  let π : ContRepresentation ℝ G V := ContRepresentation.ofMonoidHom
    { toFun g := LinearMap.toContinuousLinearMap (DistribSMul.toLinearMap ℝ V g)
      map_one' := by ext; simp
      map_mul' g h := by ext; simp [mul_smul] }
  have hπ : Continuous π := continuous_clm_apply.2 fun v ↦
    (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := 𝓘(ℝ, V)) (n := 1) v).continuous
  obtain ⟨J, hJ, hπJ⟩ := exists_compatible_forall_isComplexLinearMap ω π hπ hω
  refine ⟨J, hJ, isComplexLinearMap_fundamentalLinearMap fun g v ↦ ?_⟩
  exact ((isComplexLinearMap_iff_apply _ _ _).1 (hπJ g) v).symm

variable (I G ω)

/-- **The Hessian of a component of the quadratic moment map.** At every point, the Hessian of
`μ^ξ(v) = ½ ω(ξ_V v, v)` is the quadratic form `v ↦ ω(ξ_V v, v)`. -/
theorem hessianQuadraticForm_linearActionMomentMap_apply [FiniteDimensional ℝ V]
    (ξ : GroupLieAlgebra I G) (x v : V) :
    hessianQuadraticForm (fun y ↦ linearActionMomentMap I G ω y ξ) x v =
      ω (fundamentalLinearMap I G V ξ v) v := by
  -- `μ^ξ` is `z ↦ B z z` for the continuous bilinear form `B u w = ½ ω(ξ_V u, w)`.
  let B : V →L[ℝ] V →L[ℝ] ℝ := (2⁻¹ : ℝ) • ω.toBilinForm.toContinuousBilinearMap.comp
    (LinearMap.toContinuousLinearMap (fundamentalLinearMap I G V ξ))
  have hB : (fun y ↦ linearActionMomentMap I G ω y ξ) = fun z ↦ B z z := by
    funext z
    simp [B, div_eq_inv_mul]
  rw [hessianQuadraticForm_apply, hB, ContinuousLinearMap.fderiv_fderiv_apply_self]
  simp only [B, add_apply, ContinuousLinearMap.flip_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_comp, Function.comp_apply, LinearMap.coe_toContinuousLinearMap',
    LinearMap.toContinuousBilinearMap_apply]
  ring

/-- **The critical set of a component of the quadratic moment map.** The point `x` is a critical
point of `μ^ξ(v) = ½ ω(ξ_V v, v)` exactly when `ξ_V x = 0`. -/
theorem fderiv_linearActionMomentMap_apply_eq_zero_iff [FiniteDimensional ℝ V]
    (hω : ∀ (g : G) (u w : V), ω (g • u) (g • w) = ω u w) (ξ : GroupLieAlgebra I G) (x : V) :
    fderiv ℝ (fun y ↦ linearActionMomentMap I G ω y ξ) x = 0 ↔
      fundamentalLinearMap I G V ξ x = 0 := by
  simp only [linearActionMomentMap_apply_eq_linearMomentMap ω hω]
  rw [ContinuousLinearMap.ext_iff]
  simp only [fderiv_linearMomentMap_apply, zero_apply]
  exact ⟨fun h ↦ ω.nondegenerate.1 _ h, fun h w ↦ by simp [h]⟩

/-- The Hessian of `μ^ξ` is twice the quadratic Hamiltonian `½ ω(ξ_V v, v)` of `ξ_V`. -/
private theorem hessianQuadraticForm_linearActionMomentMap_eq_smul [FiniteDimensional ℝ V]
    (hω : ∀ (g : G) (u w : V), ω (g • u) (g • w) = ω u w) (ξ : GroupLieAlgebra I G) (x : V) :
    hessianQuadraticForm (fun y ↦ linearActionMomentMap I G ω y ξ) x =
      (2 : ℝ) • ω.hamiltonianEndEquiv.symm ⟨fundamentalLinearMap I G V ξ,
        ω.fundamentalLinearMap_mem_skewAdjointLieSubalgebra hω ξ⟩ := by
  ext v
  rw [hessianQuadraticForm_linearActionMomentMap_apply I G ω, smul_apply,
    hamiltonianEndEquiv_symm_apply_apply, linearMomentMap_apply, smul_eq_mul]
  ring

/-- **The null space of the Hessian of a component of the quadratic moment map** is the kernel of
`ξ_V`. By `TauCeti.SymplecticForm.fderiv_linearActionMomentMap_apply_eq_zero_iff` this kernel is
the critical set of `μ^ξ`, so `μ^ξ` is a Morse–Bott function: at each critical point the null space
of the Hessian is the tangent space of the critical set. -/
theorem radical_hessianQuadraticForm_linearActionMomentMap_apply [FiniteDimensional ℝ V]
    (hω : ∀ (g : G) (u w : V), ω (g • u) (g • w) = ω u w) (ξ : GroupLieAlgebra I G) (x : V) :
    (hessianQuadraticForm (fun y ↦ linearActionMomentMap I G ω y ξ) x).radical =
      LinearMap.ker (fundamentalLinearMap I G V ξ) := by
  rw [hessianQuadraticForm_linearActionMomentMap_eq_smul I G ω hω,
    QuadraticMap.radical_smul (isUnit_iff_ne_zero.2 two_ne_zero), ← ker_hamiltonianEnd,
    ← coe_hamiltonianEndEquiv_apply, LinearEquiv.apply_symm_apply]

/-- **The Morse index of a component of the moment map of a compact action is even.** For a linear
action of a compact Lie group by linear symplectomorphisms, the Morse index of
`μ^ξ(v) = ½ ω(ξ_V v, v)` is even at every point. -/
theorem even_morseIndex_linearActionMomentMap_apply [IsTopologicalGroup G] [CompactSpace G]
    (hω : ∀ (g : G) (u w : V), ω (g • u) (g • w) = ω u w) (ξ : GroupLieAlgebra I G) (x : V) :
    Even (morseIndex (fun y ↦ linearActionMomentMap I G ω y ξ) x) := by
  -- In infinite dimensions the index of inertia is `0`.
  by_cases hV : FiniteDimensional ℝ V
  swap
  · rw [morseIndex_def, QuadraticForm.sigNeg_eq_zero_of_not_finite _ hV]
    exact .zero
  obtain ⟨J, hJ, hξ⟩ := exists_compatible_forall_isComplexLinearMap_fundamentalLinearMap (I := I) hω
  rw [morseIndex_def, hessianQuadraticForm_linearActionMomentMap_eq_smul I G ω hω,
    QuadraticForm.sigNeg_smul_of_pos _ two_pos]
  exact even_sigNeg_hamiltonianEndEquiv_symm hJ _ (hξ ξ)

/-- **The coindex of a component of the moment map of a compact action is even.** For a linear
action of a compact Lie group by linear symplectomorphisms, the positive index of inertia of the
Hessian of `μ^ξ(v) = ½ ω(ξ_V v, v)`, the Morse index of `-μ^ξ`, is even at every point. -/
theorem even_sigPos_hessianQuadraticForm_linearActionMomentMap_apply [IsTopologicalGroup G]
    [CompactSpace G] (hω : ∀ (g : G) (u w : V), ω (g • u) (g • w) = ω u w)
    (ξ : GroupLieAlgebra I G) (x : V) :
    Even (sigPos (hessianQuadraticForm (fun y ↦ linearActionMomentMap I G ω y ξ) x)) := by
  -- In infinite dimensions the index of inertia is `0`.
  by_cases hV : FiniteDimensional ℝ V
  swap
  · rw [QuadraticForm.sigPos_eq_zero_of_not_finite _ hV]
    exact .zero
  obtain ⟨J, hJ, hξ⟩ := exists_compatible_forall_isComplexLinearMap_fundamentalLinearMap (I := I) hω
  rw [hessianQuadraticForm_linearActionMomentMap_eq_smul I G ω hω,
    QuadraticForm.sigPos_smul_of_pos _ two_pos]
  exact even_sigPos_hamiltonianEndEquiv_symm hJ _ (hξ ξ)

end TauCeti.SymplecticForm

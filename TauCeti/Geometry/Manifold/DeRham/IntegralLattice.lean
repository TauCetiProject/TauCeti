/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.FiniteDimensional
public import TauCeti.Geometry.Manifold.DeRham.PrescribedPeriods
public import TauCeti.GroupTheory.FiniteAbelian.IntegralDual

/-!
# The integral lattice in the first de Rham cohomology

A class `x ∈ H¹_dR(M)` is **integral** when its periods `⟨x, c⟩` on all classes `c ∈ H₁(M; ℤ)` of
the first integral singular homology group are integers. The integral classes form a subgroup, the
**integral lattice** `TauCeti.deRhamCohomology.integralLattice`. On a path-connected σ-compact
manifold, under the de Rham isomorphism `H¹_dR(M) ≃ Hom(H₁(M; ℤ), ℝ)` it is the image of
`Hom(H₁(M; ℤ), ℤ)` (`TauCeti.deRhamCohomology.integralLatticeEquiv`), the integral cohomology
`H¹(M; ℤ)` by the universal coefficient theorem.

Integral classes are the classes of the logarithmic derivatives of gauge transformations: on a
path-connected σ-compact manifold, `x` is integral exactly when `2πi x` has the periods of
`dlog u` for a smooth map `u : M → U(1)`
(`TauCeti.deRhamCohomology.mem_integralLattice_iff_exists_circle`). In the abelian gauge theory of
a Hermitian line bundle, the integral lattice is therefore the image of the gauge group under
`u ↦ (2πi)⁻¹ [dlog u]`; these are the classes by which large gauge transformations translate the
harmonic part of a connection.

When `M` is moreover compact and boundaryless, or more generally when `H₁(M; ℤ)` is finitely
generated, the integral lattice is a full lattice: it is the `ℤ`-span of a basis
`θ₁, …, θ_b` of `H¹_dR(M)`, `b = dim H¹_dR(M)` (`TauCeti.deRhamCohomology.span_integralBasis`).
In the coordinates of this basis, a linear isomorphism `H¹_dR(M) ≃ ℝ^b`, it is `ℤ^b`
(`TauCeti.deRhamCohomology.mem_integralLattice_iff_integralBasis_repr`), and it is a free abelian
group of rank `b` (`TauCeti.deRhamCohomology.finrank_integralLattice`). The coordinates are the
periods on integral classes `c₁, …, c_b ∈ H₁(M; ℤ)` dual to the basis: `⟨θ_i, c_j⟩ = δ_ij`. Torsion
classes have vanishing real periods, so they do not obstruct integrality. The basis comes from the
corresponding statement for the real dual of a finitely generated abelian group
(`AddCommGroup.exists_basis_addMonoidHom`), transported along the de Rham isomorphism
`TauCeti.deRhamCohomology.homologyPeriodEquiv`.

Unlike the period-dual basis `TauCeti.deRhamCohomology.periodDualBasis`, whose period classes are
only required to give coordinates on `H¹_dR(M)`, the integral basis spans exactly the integral
classes over `ℤ`.

## Main definitions

* `TauCeti.deRhamCohomology.integralLattice`: the classes with integral periods on `H₁(M; ℤ)`.
* `TauCeti.deRhamCohomology.integralLatticeEquiv`: the integral lattice is `Hom(H₁(M; ℤ), ℤ)`.
* `TauCeti.deRhamCohomology.integralBasis`: a basis of `H¹_dR(M)` whose `ℤ`-span is the integral
  lattice.
* `TauCeti.deRhamCohomology.integralHomologyClass`: the integral classes on which the periods are
  the coordinates in the integral basis.
* `TauCeti.deRhamCohomology.integralLatticeBasis`: the integral basis as a `ℤ`-basis of the
  integral lattice.

## Main results

* `TauCeti.deRhamCohomology.mem_integralLattice_iff_exists_circle`: integral classes are the
  classes of `(2πi)⁻¹ dlog u` for smooth circle-valued maps `u`.
* `TauCeti.deRhamCohomology.span_integralBasis`: the integral lattice is the `ℤ`-span of the
  integral basis.
* `TauCeti.deRhamCohomology.mem_integralLattice_iff_integralBasis_repr`: a class is integral
  exactly when its coordinates in the integral basis are integers.
* `TauCeti.deRhamCohomology.finrank_integralLattice`: the integral lattice has rank
  `dim H¹_dR(M)`.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics
  82, Springer, 1982, §5 (integral de Rham classes).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996 (the components of the
  gauge group of a line bundle).
-/

public section

noncomputable section

open Module Submodule
open scoped ContDiff Manifold Real

namespace TauCeti

namespace deRhamCohomology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ### Integral classes -/

variable (I M) in
/-- The **integral lattice** of `H¹_dR(M)`: the classes whose periods on every class of the first
integral singular homology group `H₁(M; ℤ)` are integers. -/
def integralLattice : Submodule ℤ (deRhamCohomology I M 1) where
  carrier := {x | ∀ c, ∃ n : ℤ, homologyPeriod x c = n}
  add_mem' {x y} hx hy c := by
    obtain ⟨m, hm⟩ := hx c
    obtain ⟨n, hn⟩ := hy c
    exact ⟨m + n, by simp [hm, hn]⟩
  zero_mem' _ := ⟨0, by simp⟩
  smul_mem' k x hx c := by
    obtain ⟨n, hn⟩ := hx c
    exact ⟨k * n, by simp [hn]⟩

/-- A class is integral exactly when all its periods on `H₁(M; ℤ)` are integers. -/
@[simp]
theorem mem_integralLattice {x : deRhamCohomology I M 1} :
    x ∈ integralLattice I M ↔ ∀ c, ∃ n : ℤ, homologyPeriod x c = n :=
  Iff.rfl

/-! ### Integral homomorphisms and gauge transformations -/

section Connected

variable [SigmaCompactSpace M] [PathConnectedSpace M]

/-- The class with periods `g`, for a homomorphism `g : H₁(M; ℤ) → ℤ`, as an integral class. -/
private def integralLatticeMap :
    (((singularChains ℤ).obj (.of M)).homology 1 →+ ℤ) →ₗ[ℤ] integralLattice I M where
  toFun g := ⟨(homologyPeriodEquiv I M).symm ((Int.castAddHom ℝ).comp g), fun c ↦ ⟨g c, by simp⟩⟩
  map_add' _ _ := Subtype.ext <| homologyPeriod_injective <| AddMonoidHom.ext fun _ ↦ by simp
  map_smul' _ _ := Subtype.ext <| homologyPeriod_injective <| AddMonoidHom.ext fun _ ↦ by simp

private theorem homologyPeriod_integralLatticeMap
    (g : ((singularChains ℤ).obj (.of M)).homology 1 →+ ℤ)
    (c : ((singularChains ℤ).obj (.of M)).homology 1) :
    homologyPeriod (integralLatticeMap (I := I) g : deRhamCohomology I M 1) c = g c := by
  simp [integralLatticeMap]

private theorem bijective_integralLatticeMap :
    Function.Bijective (integralLatticeMap (I := I) (M := M)) := by
  refine ⟨fun g g' h ↦ AddMonoidHom.ext fun c ↦ Int.cast_injective (α := ℝ) ?_, fun x ↦ ?_⟩
  · rw [← homologyPeriod_integralLatticeMap (I := I), h, homologyPeriod_integralLatticeMap]
  · -- The integer periods of an integral class form a homomorphism `H₁(M; ℤ) → ℤ`.
    choose n hn using x.property
    have hadd (a b : ((singularChains ℤ).obj (.of M)).homology 1) : n (a + b) = n a + n b :=
      Int.cast_injective (α := ℝ) <| by push_cast; rw [← hn, ← hn, ← hn, map_add]
    refine ⟨AddMonoidHom.mk' n hadd,
      Subtype.ext (homologyPeriod_injective (AddMonoidHom.ext fun c ↦ ?_))⟩
    rw [homologyPeriod_integralLatticeMap, AddMonoidHom.mk'_apply, hn]

variable (I M) in
/-- **The integral lattice is `Hom(H₁(M; ℤ), ℤ)`**, the first integral cohomology by the universal
coefficient theorem. On a path-connected σ-compact manifold, every homomorphism
`g : H₁(M; ℤ) → ℤ` is the period homomorphism of exactly one integral class
(`TauCeti.deRhamCohomology.homologyPeriod_integralLatticeEquiv`). -/
def integralLatticeEquiv :
    (((singularChains ℤ).obj (.of M)).homology 1 →+ ℤ) ≃ₗ[ℤ] integralLattice I M :=
  .ofBijective integralLatticeMap bijective_integralLatticeMap

/-- The periods of the integral class `integralLatticeEquiv I M g` are the integers `g c`. -/
@[simp]
theorem homologyPeriod_integralLatticeEquiv
    (g : ((singularChains ℤ).obj (.of M)).homology 1 →+ ℤ)
    (c : ((singularChains ℤ).obj (.of M)).homology 1) :
    homologyPeriod (integralLatticeEquiv I M g : deRhamCohomology I M 1) c = g c :=
  homologyPeriod_integralLatticeMap g c

/-- The homomorphism `H₁(M; ℤ) → ℤ` attached to an integral class `x` takes the periods of `x`. -/
@[simp]
theorem intCast_integralLatticeEquiv_symm_apply (x : integralLattice I M)
    (c : ((singularChains ℤ).obj (.of M)).homology 1) :
    (((integralLatticeEquiv I M).symm x c : ℤ) : ℝ) =
      homologyPeriod (x : deRhamCohomology I M 1) c := by
  conv_rhs => rw [← (integralLatticeEquiv I M).apply_symm_apply x]
  rw [homologyPeriod_integralLatticeEquiv]

/-- **Integral classes are the classes of gauge transformations.** On a path-connected σ-compact
manifold, a class `x ∈ H¹_dR(M)` is integral exactly when there is a smooth circle-valued map `u`
with `∫_c dlog u = 2πi ⟨x, c⟩` for every class `c ∈ H₁(M; ℤ)`, that is, when `2πi x` is the class
of `dlog u`. -/
theorem mem_integralLattice_iff_exists_circle {x : deRhamCohomology I M 1} :
    x ∈ integralLattice I M ↔ ∃ u : C^∞⟮I, M; 𝓡 1, Circle⟯, ∀ c,
      homologyPeriodHom (mlogDeriv I fun y ↦ (u y : ℂ)) c =
        homologyPeriod x c * (2 * π * Complex.I) := by
  refine ⟨fun hx ↦ ?_, fun ⟨u, hu⟩ c ↦ ?_⟩
  · -- A gauge transformation whose periods are those of `x`.
    obtain ⟨g, hg⟩ := (integralLatticeEquiv I M).surjective ⟨x, hx⟩
    obtain ⟨u, hu⟩ := circlePeriodHom_surjective (I := I) (Multiplicative.ofAdd g)
    have hxg : x = integralLatticeEquiv I M g := (congrArg Subtype.val hg).symm
    refine ⟨u, fun c ↦ ?_⟩
    rw [u.homologyPeriodHom_mlogDeriv_eq_circlePeriodHom]
    simp [hu, hxg]
  · -- The periods of `dlog u` are `2πi` times integers.
    refine ⟨Multiplicative.toAdd (circlePeriodHom I M u) c, Complex.ofReal_injective ?_⟩
    refine mul_right_cancel₀ Complex.two_pi_I_ne_zero ?_
    rw [← hu, u.homologyPeriodHom_mlogDeriv_eq_circlePeriodHom, Complex.ofReal_intCast]

/-! ### The integral basis -/

variable [AddGroup.FG (((singularChains ℤ).obj (.of M)).homology 1)]

/-- **The integral lattice is a full lattice.** If `H₁(M; ℤ)` is finitely generated, there are
integral classes `c₁, …, c_b ∈ H₁(M; ℤ)`, `b = dim H¹_dR(M)`, and a basis of `H¹_dR(M)` whose
coordinates are the periods on the `c_i` and whose `ℤ`-span is the integral lattice. -/
theorem exists_integralBasis :
    ∃ (c : Fin (finrank ℝ (deRhamCohomology I M 1)) →
        ((singularChains ℤ).obj (.of M)).homology 1)
      (θ : Basis (Fin (finrank ℝ (deRhamCohomology I M 1))) ℝ (deRhamCohomology I M 1)),
      (∀ x i, θ.repr x i = homologyPeriod x (c i)) ∧
        span ℤ (Set.range θ) = integralLattice I M := by
  obtain ⟨n, c, b, hrepr, hspan⟩ :=
    AddCommGroup.exists_basis_addMonoidHom ℝ (((singularChains ℤ).obj (.of M)).homology 1)
  -- Transport the integral basis of `Hom(H₁(M; ℤ), ℝ)` along the de Rham isomorphism.
  let θ := b.map (homologyPeriodEquiv I M).symm
  have hθ (x : deRhamCohomology I M 1) (i : Fin n) : θ.repr x i = homologyPeriod x (c i) := by
    simp [θ, hrepr]
  obtain rfl : n = finrank ℝ (deRhamCohomology I M 1) := by
    rw [finrank_eq_card_basis θ, Fintype.card_fin]
  refine ⟨c, θ, hθ, SetLike.ext fun x ↦ ?_⟩
  have h := hspan (homologyPeriod x)
  rw [b.mem_span_iff_repr_mem ℤ] at h
  rw [θ.mem_span_iff_repr_mem ℤ, mem_integralLattice, ← h]
  simp [hθ, hrepr]

variable (I M)

/-- The **integral homology classes** `c₁, …, c_b ∈ H₁(M; ℤ)`, `b = dim H¹_dR(M)`: the periods on
them are the coordinates in the integral basis. -/
def integralHomologyClass :
    Fin (finrank ℝ (deRhamCohomology I M 1)) → ((singularChains ℤ).obj (.of M)).homology 1 :=
  (exists_integralBasis (I := I) (M := M)).choose

/-- The **integral basis** `θ₁, …, θ_b` of `H¹_dR(M)`: its `ℤ`-span is the integral lattice
(`TauCeti.deRhamCohomology.span_integralBasis`), and its coordinates are the periods on the
integral homology classes (`TauCeti.deRhamCohomology.integralBasis_repr_apply`). -/
def integralBasis :
    Basis (Fin (finrank ℝ (deRhamCohomology I M 1))) ℝ (deRhamCohomology I M 1) :=
  (exists_integralBasis (I := I) (M := M)).choose_spec.choose

variable {I M}

/-- The coordinates of a class in the integral basis are its periods on the integral homology
classes. -/
@[simp]
theorem integralBasis_repr_apply (x : deRhamCohomology I M 1)
    (i : Fin (finrank ℝ (deRhamCohomology I M 1))) :
    (integralBasis I M).repr x i = homologyPeriod x (integralHomologyClass I M i) :=
  (exists_integralBasis (I := I) (M := M)).choose_spec.choose_spec.1 x i

/-- The integral basis is dual to the integral homology classes: `⟨θ_i, c_j⟩ = δ_ij`. -/
@[simp]
theorem homologyPeriod_integralBasis_integralHomologyClass
    (i j : Fin (finrank ℝ (deRhamCohomology I M 1))) :
    homologyPeriod (integralBasis I M i) (integralHomologyClass I M j) =
      if i = j then 1 else 0 := by
  rw [← integralBasis_repr_apply, Basis.repr_self, Finsupp.single_apply]

variable (I M) in
/-- **The integral lattice is the `ℤ`-span of the integral basis.** -/
theorem span_integralBasis : span ℤ (Set.range (integralBasis I M)) = integralLattice I M :=
  (exists_integralBasis (I := I) (M := M)).choose_spec.choose_spec.2

/-- The vectors of the integral basis are integral classes. -/
theorem integralBasis_mem_integralLattice (i : Fin (finrank ℝ (deRhamCohomology I M 1))) :
    integralBasis I M i ∈ integralLattice I M :=
  span_integralBasis I M ▸ subset_span (Set.mem_range_self i)

/-- A class is integral exactly when its coordinates in the integral basis are integers, that is,
when its periods on the integral homology classes are integers. -/
theorem mem_integralLattice_iff_integralBasis_repr {x : deRhamCohomology I M 1} :
    x ∈ integralLattice I M ↔ ∀ i, ∃ n : ℤ, (integralBasis I M).repr x i = n := by
  rw [← span_integralBasis, (integralBasis I M).mem_span_iff_repr_mem ℤ]
  simp [eq_comm]

variable (I M) in
/-- The integral basis, as a `ℤ`-basis of the integral lattice. -/
def integralLatticeBasis :
    Basis (Fin (finrank ℝ (deRhamCohomology I M 1))) ℤ (integralLattice I M) :=
  ((integralBasis I M).restrictScalars ℤ).map (LinearEquiv.ofEq _ _ (span_integralBasis I M))

@[simp]
theorem coe_integralLatticeBasis (i : Fin (finrank ℝ (deRhamCohomology I M 1))) :
    (integralLatticeBasis I M i : deRhamCohomology I M 1) = integralBasis I M i := by
  simp [integralLatticeBasis]

/-- The integer coordinates of an integral class in the integral lattice basis are its periods on
the integral homology classes. -/
@[simp]
theorem intCast_integralLatticeBasis_repr_apply (x : integralLattice I M)
    (i : Fin (finrank ℝ (deRhamCohomology I M 1))) :
    ((integralLatticeBasis I M).repr x i : ℝ) =
      homologyPeriod (x : deRhamCohomology I M 1) (integralHomologyClass I M i) := by
  rw [← integralBasis_repr_apply, ← eq_intCast (algebraMap ℤ ℝ)]
  exact (integralBasis I M).restrictScalars_repr_apply ℤ _ i

instance : Module.Free ℤ (integralLattice I M) :=
  .of_basis (integralLatticeBasis I M)

instance : Module.Finite ℤ (integralLattice I M) :=
  .of_basis (integralLatticeBasis I M)

variable (I M) in
/-- **The integral lattice has full rank**: its rank is `dim H¹_dR(M)`. -/
theorem finrank_integralLattice :
    finrank ℤ (integralLattice I M) = finrank ℝ (deRhamCohomology I M 1) := by
  rw [finrank_eq_card_basis (integralLatticeBasis I M), Fintype.card_fin]

end Connected

end deRhamCohomology

end TauCeti

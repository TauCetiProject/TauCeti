/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.NormalBasis
public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.NumberTheory.LocalField.GaloisAction
public import TauCeti.NumberTheory.LocalField.IntegerRing

/-!
# Galois-stable lattices from normal bases of local fields

Let `L/K` be a finite Galois extension of nonarchimedean local fields with Galois group
`G = L ≃ₐ[K] L`. By the normal basis theorem (`IsGalois.normalBasis`) there is `α ∈ L` whose
conjugates `σ α` form a `K`-basis of `L`; after multiplying by a nonzero element of `𝒪[K]` it may
be taken in `𝒪[L]`. The `𝒪[K]`-span `A` of the orbit of such an `α` is then:

* stable under `G` (Mathlib's `Module.End.span_orbit_mem_invtSubmodule`);
* free over `𝒪[K]` on the conjugates of `α`, that is, free of rank one over the group ring
  `𝒪[K][G]` with generator `α` (`TauCeti.spanOrbitEquiv`);
* open in `𝒪[L]`: it contains a power of the maximal ideal `𝓂[L]`.

In general `𝒪[L]` itself is not free over `𝒪[K][G]` (this holds only for tamely ramified
extensions), so the lattice `A` is the substitute. Scaling `α` further by a nonzero element of
`𝒪[K]` shrinks `A` without changing these properties, and makes it nearly closed under
multiplication: for any nonzero `ϖ ∈ 𝒪[K]` one can arrange `A * A ≤ ϖ • A`. For `ϖ` a
uniformizer this is the condition under which the sets `1 + ϖ ^ j • A` form a decreasing chain of
Galois-stable open subgroups of the units of `𝒪[L]`, with every successive quotient isomorphic to
`A / ϖ • A`, a free module over the group ring `(𝒪[K] ⧸ ϖ)[G]`. Such a filtration of the local
units is how their Herbrand quotient is computed in the cyclic case.

## Main definitions

* `TauCeti.spanOrbitEquiv`: the isomorphism of representations from the group ring `𝒪[K][G]` onto
  the `𝒪[K]`-span of the orbit of an element of `𝒪[L]` whose conjugates form a `K`-basis of `L`.

## Main results

* `TauCeti.exists_linearIndependent_algEquiv_apply_integerRing`: some element of `𝒪[L]` has
  conjugates forming a `K`-basis of `L`.
* `TauCeti.linearIndependent_smul_integerRing`: the conjugates of such an element are linearly
  independent over `𝒪[K]`.
* `TauCeti.exists_pow_maximalIdeal_le_span_orbit`: the `𝒪[K]`-span of the orbit of such an
  element contains a power of `𝓂[L]`.
* `TauCeti.exists_span_orbit_mul_le_smul`: for every nonzero `ϖ ∈ 𝒪[K]` there is such an element
  whose orbit spans a lattice `A` with `A * A ≤ ϖ • A`.

These elements lie in `𝒪[L]` and their conjugates form a `K`-basis of `L`; they need not give an
`𝒪[K]`-basis of `𝒪[L]`.

## References

* J.-P. Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VI.
* J. Neukirch, *Algebraic Number Theory*, Chapter V, §1.
-/

public section

open ValuativeRel IsLocalRing Submodule MulAction
open scoped Pointwise

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- If the conjugates of an element of `𝒪[L]` are linearly independent over `K`, they are linearly
independent over `𝒪[K]` as elements of `𝒪[L]`. -/
theorem linearIndependent_smul_integerRing {α : 𝒪[L]}
    (h : LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ (α : L)) :
    LinearIndependent 𝒪[K] fun σ : L ≃ₐ[K] L ↦ σ • α :=
  .of_comp (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L).toLinearMap <| by
    convert h.restrict_scalars' (R := 𝒪[K]) using 1
    ext σ
    simp [Algebra.algebraMap_ofSubsemiring_apply]

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- **The span of the orbit is free of rank one over the group ring.** If the conjugates of
`α ∈ 𝒪[L]` are linearly independent over `K`, then `∑ σ, r_σ σ ↦ ∑ σ, r_σ • σ α` is an
isomorphism from the group ring `𝒪[K][G]`, with `G` acting by left multiplication, onto the
`𝒪[K]`-span of the orbit of `α`, with the Galois action restricted from `𝒪[L]`. -/
noncomputable def spanOrbitEquiv {α : 𝒪[L]}
    (h : LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ (α : L)) :
    (Representation.leftRegular 𝒪[K] (L ≃ₐ[K] L)).Equiv
      ((Representation.ofDistribMulAction 𝒪[K] (L ≃ₐ[K] L) 𝒪[L]).subrepresentation
        (span 𝒪[K] (orbit (L ≃ₐ[K] L) α))
        fun σ ↦ (Module.End.mem_invtSubmodule _).1 <|
          Module.End.span_orbit_mem_invtSubmodule _ α σ) :=
  .mk ((MonoidAlgebra.coeffLinearEquiv 𝒪[K]).trans
    (linearIndependent_smul_integerRing h).linearCombinationEquiv) fun τ ↦ by
    ext σ : 2
    refine Subtype.ext ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply,
      Representation.ofMulAction_single, smul_eq_mul, LinearEquiv.coe_coe,
      Representation.subrepresentation_apply, LinearMap.coe_restrict_apply,
      Representation.ofDistribMulAction_apply_apply]
    change Finsupp.linearCombination 𝒪[K] (fun σ : L ≃ₐ[K] L ↦ σ • α) (.single (τ * σ) 1) =
      τ • Finsupp.linearCombination 𝒪[K] (fun σ : L ≃ₐ[K] L ↦ σ • α) (.single σ 1)
    simp [mul_smul]

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- `spanOrbitEquiv` sends `r σ ∈ 𝒪[K][G]` to `r • σ α`. -/
@[simp]
theorem coe_spanOrbitEquiv_single {α : 𝒪[L]}
    (h : LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ (α : L)) (σ : L ≃ₐ[K] L) (r : 𝒪[K]) :
    (spanOrbitEquiv h (MonoidAlgebra.single σ r) : 𝒪[L]) = r • σ • α := by
  change Finsupp.linearCombination 𝒪[K] (fun σ : L ≃ₐ[K] L ↦ σ • α) (.single σ r) = _
  simp

variable [IsGalois K L]

variable (K L) in
/-- Some element of `𝒪[L]` has conjugates forming a `K`-basis of `L`: a normal basis element of
`L/K` scaled into `𝒪[L]`. -/
theorem exists_linearIndependent_algEquiv_apply_integerRing :
    ∃ α : 𝒪[L], LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ (α : L) := by
  obtain ⟨a, ha, hmem⟩ := exists_algebraMap_mul_mem_integerRing K L (IsGalois.normalBasis K L 1)
  have ha' : (a : K) ≠ 0 := fun h ↦ ha (Subtype.ext h)
  refine ⟨⟨_, hmem⟩, ?_⟩
  convert (IsGalois.normalBasis K L).linearIndependent.units_smul
    (fun _ ↦ Units.mk0 (a : K) ha') using 1
  ext σ
  rw [Pi.smul_apply', IsGalois.normalBasis_apply σ]
  simp [Algebra.smul_def]

/-- A nonzero element of `𝒪[K]` carries all of `𝒪[L]` into the `𝒪[K]`-span of the orbit of an
element of `𝒪[L]` whose conjugates form a `K`-basis of `L`. -/
private theorem exists_smul_mem_span_orbit {α : 𝒪[L]}
    (h : LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ (α : L)) :
    ∃ d : 𝒪[K], d ≠ 0 ∧ ∀ x : 𝒪[L], d • x ∈ span 𝒪[K] (orbit (L ≃ₐ[K] L) α) := by
  -- The conjugates of `α` form a `K`-basis `v` of `L`; clear the denominators of the coordinates
  -- in `v` of an `𝒪[K]`-basis `e` of `𝒪[L]`.
  let v : Module.Basis (L ≃ₐ[K] L) K L :=
    basisOfLinearIndependentOfCardEqFinrank h <| by
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  let e := Module.Free.chooseBasis 𝒪[K] 𝒪[L]
  let f := IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors 𝒪[K]) fun p : Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L] × (L ≃ₐ[K] L) ↦
      v.repr (f (e p.1)) p.2
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun x ↦ ?_⟩
  rw [← e.sum_repr x, Finset.smul_sum]
  refine sum_mem fun i _ ↦ ?_
  rw [smul_comm]
  refine smul_mem _ _ ?_
  choose c hc using fun σ ↦ hint (i, σ)
  have hsum : d • e i = ∑ σ, c σ • σ • α := by
    apply FaithfulSMul.algebraMap_injective 𝒪[L] L
    rw [← IsScalarTower.coe_toAlgHom' 𝒪[K], map_smul, map_sum, ← v.sum_repr (f (e i)),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [map_smul, ← algebraMap_smul K (c σ), hc σ, smul_assoc]
    simp [v, f, Algebra.algebraMap_ofSubsemiring_apply]
  rw [hsum]
  exact sum_mem fun σ _ ↦ smul_mem _ _ (subset_span (mem_orbit α σ))

/-- **The span of the orbit is open**: if the conjugates of `α ∈ 𝒪[L]` form a `K`-basis of `L`,
the `𝒪[K]`-span of the orbit of `α` contains a power of the maximal ideal of `𝒪[L]`. -/
theorem exists_pow_maximalIdeal_le_span_orbit {α : 𝒪[L]}
    (h : LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ (α : L)) :
    ∃ n : ℕ, (𝓂[L] ^ n).restrictScalars 𝒪[K] ≤ span 𝒪[K] (orbit (L ≃ₐ[K] L) α) := by
  obtain ⟨d, hd, hdα⟩ := exists_smul_mem_span_orbit h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hd' : Ideal.span {algebraMap 𝒪[K] 𝒪[L] d} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective 𝒪[K] 𝒪[L])).2 hd
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hd' hϖ
  refine ⟨n, fun x hx ↦ ?_⟩
  rw [restrictScalars_mem, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    Ideal.span_singleton_pow, ← hn, Ideal.mem_span_singleton'] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [mul_comm, ← Algebra.smul_def]
  exact hdα y

/-- **A Galois-stable lattice that is almost closed under multiplication.** For every nonzero
`ϖ ∈ 𝒪[K]` there is `α ∈ 𝒪[L]` whose conjugates form a `K`-basis of `L` such that the
`𝒪[K]`-span `A` of its orbit satisfies `A * A ≤ ϖ • A`. By `spanOrbitEquiv` and
`exists_pow_maximalIdeal_le_span_orbit`, this `A` is free of rank one over `𝒪[K][G]` on `α` and
contains a power of `𝓂[L]`. -/
theorem exists_span_orbit_mul_le_smul {ϖ : 𝒪[K]} (hϖ : ϖ ≠ 0) :
    ∃ α : 𝒪[L], LinearIndependent K (fun σ : L ≃ₐ[K] L ↦ σ (α : L)) ∧
      span 𝒪[K] (orbit (L ≃ₐ[K] L) α) * span 𝒪[K] (orbit (L ≃ₐ[K] L) α) ≤
        ϖ • span 𝒪[K] (orbit (L ≃ₐ[K] L) α) := by
  obtain ⟨β, hβ⟩ := exists_linearIndependent_algEquiv_apply_integerRing K L
  obtain ⟨d, hd, hdβ⟩ := exists_smul_mem_span_orbit hβ
  -- Scale `β` by `c = ϖ * d`: then `A = c • span (orbit β)`, and for `a₀, b₀` in the span of the
  -- orbit of `β`, `(c • a₀) * (c • b₀) = ϖ • c • (d • (a₀ * b₀))` with `d • (a₀ * b₀)` back in
  -- that span.
  set c := ϖ * d
  have hc : (c : K) ≠ 0 := fun h ↦ mul_ne_zero hϖ hd (Subtype.ext h)
  have hα : LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ ((c • β : 𝒪[L]) : L) := by
    convert hβ.units_smul fun _ ↦ Units.mk0 (c : K) hc using 1
    ext σ
    simp [Algebra.smul_def]
  refine ⟨c • β, hα, ?_⟩
  have hspan : span 𝒪[K] (orbit (L ≃ₐ[K] L) (c • β)) =
      c • span 𝒪[K] (orbit (L ≃ₐ[K] L) β) := by
    rw [smul_span]
    congr 1
    ext x
    simp only [Set.mem_smul_set, mem_orbit_iff]
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨σ • β, ⟨σ, rfl⟩, (smul_comm σ c β).symm⟩
    · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
      exact ⟨σ, smul_comm σ c β⟩
  rw [mul_le]
  intro a ha b hb
  rw [hspan] at ha hb
  obtain ⟨a₀, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).1 ha
  obtain ⟨b₀, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).1 hb
  have hmem : c • (d • (a₀ * b₀)) ∈ span 𝒪[K] (orbit (L ≃ₐ[K] L) (c • β)) :=
    hspan ▸ smul_mem_pointwise_smul _ _ _ (hdβ _)
  convert smul_mem_pointwise_smul _ ϖ _ hmem using 1
  simp only [c, Algebra.smul_def, map_mul]
  ring

end TauCeti

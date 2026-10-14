/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact
public import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# The trace short exact sequence of an open subgroup

For an open subgroup `U` of finite index in a topological group `G` and a discrete `G`-module `M`,
the trace `Coind_U^G M → M` of `TauCeti.DiscreteCoind.trace` is surjective
(`TauCeti.DiscreteCoind.trace_surjective`). Its kernel `TauCeti.DiscreteCoind.traceKer` is a
`G`-stable additive subgroup of the coinduced module, hence a discrete `G`-module in its own right,
and the three fit into the short exact sequence

```text
0 → traceKer G U M → Coind_U^G M → M → 0
```

of discrete `G`-modules, `TauCeti.DiscreteCoind.traceShortExact`. Its long exact cohomology
sequence compares `Hⁿ(G, Coind_U^G M) ≅ Hⁿ(U, M)` with `Hⁿ(G, M)` through the cohomology of the
kernel; this is how the cohomological dimension of `G` is bounded by that of an open subgroup
(Serre, *Galois Cohomology*, Ch. I, §3.3, Prop. 14).

For a normal subgroup `V`, conjugation by `g : G` is a `G`-equivariant endomorphism
`TauCeti.DiscreteCoind.conj V V M g` of `Coind_V^G M`, `f ↦ (x ↦ g • f (g⁻¹ x))`: under
`Coind_V^G M ≅ ℤ[G ⧸ V] ⊗ M` it is right multiplication by `g`. It commutes with the trace, and
the differences `conj σ - 1` cover the kernel of the trace: the image of the `G`-equivariant
map `∏_{x ∈ G ⧸ V} Coind_V^G M → Coind_V^G M`, `(φ_x)_x ↦ ∑_x (conj x.out⁻¹ - 1) φ_x`, is
exactly `traceKer G V M`. This is the cover `⊕_σ ℤ[G ⧸ V] ⊗ M → I ⊗ M`,
`e_σ ⊗ m ↦ (σ - 1) ⊗ m`, of NSW's proof of (3.3.11), `I` being the augmentation ideal of
`ℤ[G ⧸ V]`. A preimage is computed from the
decomposition into singles (`TauCeti.DiscreteCoind.sum_single`): conjugation by `g` moves the
single at `1` to the single at `g`, and the singles at `1` add up to the single of the trace.

## Main definitions

* `TauCeti.DiscreteCoind.traceKer`: the kernel of the trace, a `G`-stable additive subgroup of
  `Coind_U^G M`, with the restricted action of `G` and its continuity as instances.
* `TauCeti.DiscreteCoind.traceShortExact`: the short exact sequence
  `0 → traceKer G U M → Coind_U^G M → M → 0` for an open subgroup `U`.
* `TauCeti.DiscreteCoind.traceKerCover`: for a normal subgroup `V`, the cover
  `∏_{G ⧸ V} Coind_V^G M →+[G] Coind_V^G M` by the conjugation differences `conj σ - 1`, whose
  image is `traceKer G V M`.
* `TauCeti.DiscreteCoind.traceKerCoverShortExact`: the short exact sequence
  `0 → traceKerCoverKer V M → ∏_{G ⧸ V} Coind_V^G M → traceKer G V M → 0` of the cover, whose
  second map is the codrestriction of `traceKerCover` to `traceKer G V M`.

## Main results

* `TauCeti.DiscreteCoind.isPPrimaryTorsion_traceKer`: over a compact group the kernel of the trace
  of a discrete `p`-primary torsion module is `p`-primary torsion.
* `TauCeti.DiscreteCoind.conj_single_one`: conjugation by `g` moves the single at `1` with value
  `a` to the single at `g` with value `g • a`.
* `TauCeti.DiscreteCoind.range_traceKerCover`: the image of the cover is exactly the kernel of
  the trace.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.3, Prop. 14.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of (3.3.11).
-/

public section

namespace TauCeti.DiscreteCoind

universe u v

variable (G : Type u) [Group G] [TopologicalSpace G] [ContinuousMul G] (U : Subgroup G)
  [U.FiniteIndex] (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/-! ### The kernel of the trace -/

/-- **The kernel of the trace** `Coind_U^G M → M`, as an additive subgroup of the coinduced
module. It is `G`-stable (`TauCeti.DiscreteCoind.smul_mem_traceKer`), and carries the restricted
action of `G` as an instance. -/
noncomputable def traceKer : AddSubgroup (DiscreteCoind G U M) := (trace G U M).toAddMonoidHom.ker

variable {G U M}

@[simp]
theorem mem_traceKer_iff {f : DiscreteCoind G U M} : f ∈ traceKer G U M ↔ trace G U M f = 0 :=
  Iff.rfl

/-- The kernel of the trace is stable under the action of `G`, the trace being equivariant. -/
theorem smul_mem_traceKer (g : G) {f : DiscreteCoind G U M} (hf : f ∈ traceKer G U M) :
    g • f ∈ traceKer G U M := by
  rw [mem_traceKer_iff] at hf ⊢
  rw [_root_.map_smul, hf, smul_zero]

variable (G U M)

/-- The action of `G` on the kernel of the trace, by restriction. -/
noncomputable instance : DistribMulAction G (traceKer G U M) :=
  (traceKer G U M).restrictDistribMulAction fun g _ hf ↦ smul_mem_traceKer g hf

/-- The inclusion of the kernel of the trace in `Coind_U^G M` is equivariant. -/
@[simp]
theorem coe_smul_traceKer (g : G) (f : traceKer G U M) :
    ((g • f : traceKer G U M) : DiscreteCoind G U M) = g • (f : DiscreteCoind G U M) :=
  rfl

/-- Over a compact group, the kernel of the trace of a discrete `p`-primary torsion module is
`p`-primary torsion, as a subgroup of the `p`-primary torsion module `Coind_U^G M`. -/
theorem isPPrimaryTorsion_traceKer {p : ℕ} [CompactSpace G] [TopologicalSpace M]
    [DiscreteTopology M] (hM : IsPPrimaryTorsion p M) : IsPPrimaryTorsion p (traceKer G U M) :=
  (isPPrimaryTorsion_discreteCoind G U M hM).of_injective (traceKer G U M).subtype
    Subtype.val_injective

/-! ### The short exact sequence -/

variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- **The trace short exact sequence** `0 → traceKer G U M → Coind_U^G M → M → 0` of discrete
`G`-modules, for an open subgroup `U` of finite index and a discrete `G`-module `M`. The second
map is the trace, surjective because `U` is open. -/
noncomputable def traceShortExact (hU : IsOpen (U : Set G)) :
    ContCohomology.DiscreteShortExact G (traceKer G U M) (DiscreteCoind G U M) M where
  incl := (traceKer G U M).subtype
  proj := (trace G U M).toAddMonoidHom
  incl_equivariant _ _ := rfl
  proj_equivariant g f := _root_.map_smul (trace G U M) g f
  incl_injective := Subtype.val_injective
  proj_surjective := trace_surjective hU
  exact f := ⟨fun hf ↦ ⟨⟨f, hf⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.2⟩

variable (hU : IsOpen (U : Set G))

/-- The first map of the trace short exact sequence is the inclusion of the kernel. -/
@[simp]
theorem traceShortExact_incl : (traceShortExact G U M hU).incl = (traceKer G U M).subtype :=
  (rfl)

/-- The second map of the trace short exact sequence is the trace. -/
@[simp]
theorem traceShortExact_proj :
    (traceShortExact G U M hU).proj = (trace G U M).toAddMonoidHom :=
  (rfl)

section Compact

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G) [U.FiniteIndex] (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/-- Over a compact group the restricted action on the kernel of the trace is continuous, the
kernel being a discrete module. -/
instance : ContinuousSMul G (traceKer G U M) :=
  (traceKer G U M).restrictDistribMulAction_continuousSMul fun g _ hf ↦ smul_mem_traceKer g hf

end Compact

end TauCeti.DiscreteCoind

/-! ### The cover of the kernel of the trace of a normal subgroup -/

namespace TauCeti.DiscreteCoind

universe u v

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

-- `conj V V M g` and `trace_conj` take the normality of `V` as
-- `V.map (MulAut.conj g).toMonoidHom = V`; below, Mathlib's `Subgroup.Normal.map_conj_eq` is
-- ascribed to that form with `show`. Passed unascribed, it is stated with the coercion
-- `↑(MulAut.conj g)`, the resulting term is not type-correct at instance transparency, and
-- `conj_apply` no longer rewrites it.

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G] (V : Subgroup G) [V.Normal]
  (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/-- **Conjugation moves singles**: conjugation by `g` sends the single at `1` with value `a` to
the single at `g` with value `g • a`. -/
@[simp]
theorem conj_single_one [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul V M]
    (hV : IsOpen (V : Set G)) (g : G) (a : M) :
    conj V V M g (show V.map (MulAut.conj g).toMonoidHom = V from
        Subgroup.Normal.map_conj_eq V g).ge (single G V M hV 1 a) =
      single G V M hV g (g • a) := by
  ext x
  rw [conj_apply]
  by_cases hx : x * g⁻¹ ∈ V
  · -- `x = v g` with `v ∈ V`, then `g⁻¹ x = (g⁻¹ v g) 1`, and both sides are `v • g • a`
    obtain ⟨v, rfl⟩ : ∃ v : V, x = (v : G) * g := ⟨⟨x * g⁻¹, hx⟩, by simp⟩
    have hv : g⁻¹ * v * g ∈ V := by simpa using ‹V.Normal›.conj_mem _ v.2 g⁻¹
    have h₁ : g⁻¹ * ((v : G) * g) = ((⟨g⁻¹ * v * g, hv⟩ : V) : G) * 1 := by simp [mul_assoc]
    rw [h₁, single_apply_mul, single_apply_mul]
    simp only [Subgroup.smul_def, smul_smul]
    congr 1
    group
  · have hx' : g⁻¹ * x * (1 : G)⁻¹ ∉ V := fun h => hx (by
      simpa [mul_assoc] using ‹V.Normal›.conj_mem _ h g)
    rw [single_apply_of_notMem hV _ hx', smul_zero, single_apply_of_notMem hV _ hx]

variable [V.FiniteIndex]

/-- **The cover of the kernel of the trace by conjugation differences**: the `G`-equivariant map
`∏_{x ∈ G ⧸ V} Coind_V^G M → Coind_V^G M` sending `(φ_x)_x` to `∑_x (conj x.out⁻¹ - 1) φ_x`. Its
image is the kernel of the trace (`range_traceKerCover`). -/
noncomputable def traceKerCover : (G ⧸ V → DiscreteCoind G V M) →+[G] DiscreteCoind G V M where
  toFun φ := ∑ x : G ⧸ V,
    (conj V V M x.out⁻¹ (show V.map (MulAut.conj x.out⁻¹).toMonoidHom = V from
      Subgroup.Normal.map_conj_eq V _).ge (φ x) - φ x)
  map_zero' := by simp
  map_add' φ ψ := by
    simp only [Pi.add_apply, _root_.map_add, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by abel
  map_smul' g φ := by
    simp only [Pi.smul_apply, _root_.map_smul, MonoidHom.id_apply, Finset.smul_sum, smul_sub]

/-- The defining formula of `traceKerCover`. -/
@[simp]
theorem traceKerCover_apply (φ : G ⧸ V → DiscreteCoind G V M) :
    traceKerCover V M φ =
      ∑ x : G ⧸ V,
        (conj V V M x.out⁻¹ (show V.map (MulAut.conj x.out⁻¹).toMonoidHom = V from
          Subgroup.Normal.map_conj_eq V _).ge (φ x) - φ x) :=
  (rfl)

/-- The cover lands in the kernel of the trace, conjugation commuting with the trace. -/
theorem traceKerCover_mem_traceKer (φ : G ⧸ V → DiscreteCoind G V M) :
    traceKerCover V M φ ∈ traceKer G V M := by
  rw [mem_traceKer_iff, traceKerCover_apply, _root_.map_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [_root_.map_sub, trace_conj _ (show V.map (MulAut.conj x.out⁻¹).toMonoidHom = V from
    Subgroup.Normal.map_conj_eq V _).symm, sub_self]

/-- **The image of the cover is the kernel of the trace.** For `f` in the kernel of the trace,
the family of singles at `1` with values `x.out • f x.out⁻¹` is a preimage: conjugation moves them
to the singles decomposing `f`, and they add up to the single of the trace of `f`, which is `0`. -/
theorem range_traceKerCover [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul V M]
    (hV : IsOpen (V : Set G)) : (traceKerCover V M).toAddMonoidHom.range = traceKer G V M := by
  refine le_antisymm (fun _ ⟨φ, hφ⟩ ↦ hφ ▸ traceKerCover_mem_traceKer V M φ) fun f hf ↦ ?_
  refine ⟨fun x => single G V M hV 1 (x.out • f x.out⁻¹), (traceKerCover_apply V M _).trans ?_⟩
  rw [Finset.sum_sub_distrib, ← _root_.map_sum, ← trace_apply, (mem_traceKer_iff.1 hf),
    _root_.map_zero, sub_zero]
  refine (Finset.sum_congr rfl fun x _ => ?_).trans (sum_single hV f)
  rw [conj_single_one, smul_smul, inv_mul_cancel, one_smul]

/-- The kernel of the cover `traceKerCover`, a `G`-stable additive subgroup of
`∏_{G ⧸ V} Coind_V^G M`. -/
noncomputable def traceKerCoverKer : AddSubgroup (G ⧸ V → DiscreteCoind G V M) :=
  (traceKerCover V M).toAddMonoidHom.ker

@[simp]
theorem mem_traceKerCoverKer_iff {φ : G ⧸ V → DiscreteCoind G V M} :
    φ ∈ traceKerCoverKer V M ↔ traceKerCover V M φ = 0 :=
  Iff.rfl

/-- The kernel of the cover is stable under the action of `G`, the cover being equivariant. -/
theorem smul_mem_traceKerCoverKer (g : G) {φ : G ⧸ V → DiscreteCoind G V M}
    (hφ : φ ∈ traceKerCoverKer V M) : g • φ ∈ traceKerCoverKer V M := by
  rw [mem_traceKerCoverKer_iff] at hφ ⊢
  rw [_root_.map_smul, hφ, smul_zero]

/-- The action of `G` on the kernel of the cover, by restriction. -/
noncomputable instance : DistribMulAction G (traceKerCoverKer V M) :=
  (traceKerCoverKer V M).restrictDistribMulAction fun g _ hφ ↦ smul_mem_traceKerCoverKer V M g hφ

/-- The inclusion of the kernel of the cover in `∏_{G ⧸ V} Coind_V^G M` is equivariant. -/
@[simp]
theorem coe_smul_traceKerCoverKer (g : G) (φ : traceKerCoverKer V M) :
    ((g • φ : traceKerCoverKer V M) : G ⧸ V → DiscreteCoind G V M) =
      g • (φ : G ⧸ V → DiscreteCoind G V M) :=
  rfl

section Compact

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (V : Subgroup G) [V.Normal] [V.FiniteIndex] (M : Type v) [AddCommGroup M]
  [DistribMulAction G M]

/-- Over a compact group the restricted action on the kernel of the cover is continuous. -/
instance : ContinuousSMul G (traceKerCoverKer V M) :=
  (traceKerCoverKer V M).restrictDistribMulAction_continuousSMul
    fun g _ hφ ↦ smul_mem_traceKerCoverKer V M g hφ

end Compact

variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- **The short exact sequence of the cover**
`0 → traceKerCoverKer → ∏_{G ⧸ V} Coind_V^G M → traceKer G V M → 0` of discrete `G`-modules, for an
open normal subgroup `V` of finite index. -/
noncomputable def traceKerCoverShortExact (hV : IsOpen (V : Set G)) :
    ContCohomology.DiscreteShortExact G (traceKerCoverKer V M) (G ⧸ V → DiscreteCoind G V M)
      (traceKer G V M) where
  incl := (traceKerCoverKer V M).subtype
  proj := AddMonoidHom.codRestrict (traceKerCover V M).toAddMonoidHom _
    (traceKerCover_mem_traceKer V M)
  incl_equivariant _ _ := rfl
  proj_equivariant g φ := Subtype.ext (_root_.map_smul (traceKerCover V M) g φ)
  incl_injective := Subtype.val_injective
  proj_surjective f := by
    obtain ⟨φ, hφ⟩ := (range_traceKerCover V M hV).ge f.2
    exact ⟨φ, Subtype.ext hφ⟩
  exact φ := by
    refine ⟨fun hφ ↦ ⟨⟨φ, ?_⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact Subtype.ext a.2⟩
    exact congrArg Subtype.val hφ

/-- The first map of the cover short exact sequence is the inclusion of the kernel. -/
@[simp]
theorem traceKerCoverShortExact_incl (hV : IsOpen (V : Set G)) :
    (traceKerCoverShortExact V M hV).incl = (traceKerCoverKer V M).subtype :=
  (rfl)

/-- The second map of the cover short exact sequence, followed by the inclusion of the kernel of
the trace, is the cover. -/
@[simp]
theorem traceKerCoverShortExact_proj_apply (hV : IsOpen (V : Set G))
    (φ : G ⧸ V → DiscreteCoind G V M) :
    ((traceKerCoverShortExact V M hV).proj φ : DiscreteCoind G V M) = traceKerCover V M φ :=
  (rfl)

end TauCeti.DiscreteCoind

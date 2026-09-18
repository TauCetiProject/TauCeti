/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiveTerm
public import TauCeti.Topology.Algebra.Group.Profinite.Section
import TauCeti.Topology.Algebra.Group.LocallyConstant

/-!
# The transgression

Let `N` be a closed normal subgroup of a profinite group `G` and `M` a discrete `G`-module. The
**transgression**

```text
tg : H¹(N, M)^{G ⧸ N} → H²(G ⧸ N, M ^ N)
```

is the fourth arrow of the inflation-restriction-transgression five-term sequence

```text
0 → H¹(G ⧸ N, M ^ N) → H¹(G, M) → H¹(N, M)^{G ⧸ N} → H²(G ⧸ N, M ^ N) → H²(G, M).
```

It is defined by lifting a cocycle `c` on `N` whose class is conjugation-invariant to a continuous
cochain `f` on `G`, differentiating, and observing that `d¹ f` descends to a cocycle on `G ⧸ N`
with values in `M ^ N`. This file carries out that construction on the explicit low-degree model
and proves that the resulting class is independent of every choice made.

## The lift

A continuous cochain `f : G → M` is a *transgression lift* of `c : N → M`
(`TauCeti.ContCohomology.IsTransgressionLift`) when

```text
f (g * n) = f g + g • c n    and    g • c (g⁻¹ n g) - c n = n • f g - f g
```

for all `g : G` and `n : N`. These two identities are exactly what makes `d¹ f` constant on the
cosets of `N` in each variable and `N`-invariant in value, so it descends to
`TauCeti.ContCohomology.IsTransgressionLift.cocycle`. Lifts form a group under addition, the
coboundary of `m` on `G` lifts the coboundary of `m` on `N`, and a lift of `0` descends to a
continuous cochain on `G ⧸ N`; together these give the independence statement
`TauCeti.ContCohomology.IsTransgressionLift.cocycle_sub_mem_B2`, which says that cohomologous
functions on `N` have lifts whose descended coboundaries differ by an explicit `2`-coboundary.
None of this uses more than a topological group and a topological module.

Existence is where profiniteness enters. Given a continuous section `s` of `G → G ⧸ N`, which
`TauCeti.exists_continuous_section` supplies for closed `N`, and a continuous choice `F` of
elements trivialising the conjugates of `c`, the cochain

```text
g ↦ F (s (g N)) + s (g N) • c ((s (g N))⁻¹ * g)
```

is a lift (`TauCeti.ContCohomology.transgressionLift`, normalised to vanish at `1`). The continuous
choice of `F` is `TauCeti.ContCohomology.exists_continuous_smul_conj_sub_eq_d0`: on a compact
group the conjugate of `c` by `g` depends on `g` only through a coset of one open subgroup, by
uniform local constancy, and discreteness of `M` makes a choice on those finitely many cosets
continuous.

## Main definitions

* `TauCeti.ContCohomology.IsTransgressionLift`: the lifting condition, and
  `TauCeti.ContCohomology.IsTransgressionLift.cocycle`: the descended coboundary of a lift.
* `TauCeti.ContCohomology.transgressionLift`: the lift attached to a continuous section.
* `TauCeti.ContCohomology.transgressionCochain` and `transgressionCocycle`: the raw transgression
  `2`-cocycle on `G ⧸ N`.
* `TauCeti.ContCohomology.transgression`: the transgression as an additive map.

## Main statements

* `TauCeti.ContCohomology.transgressionCochain_apply`: the raw transgression at `(q, r)` is `d¹`
  of the lift at `(s q, s r)`.
* `TauCeti.ContCohomology.transgressionCochain_sub_mem_B2`: changing the section or the
  representative changes the raw transgression by an explicit `2`-coboundary.
* `TauCeti.ContCohomology.transgression_apply`: the transgression is the class of the raw
  transgression for every section and every representative.
* `TauCeti.ContCohomology.transgression_explicitResConj1`: transgression kills the image of
  restriction.
* `TauCeti.ContCohomology.explicitInfl2_transgression`: inflation kills the image of
  transgression.

## Implementation notes

Profiniteness and closedness of `N` are genuine hypotheses of the existence half: the lift is
built through a continuous section of `G → G ⧸ N`, and such a section does not exist for an
arbitrary topological group (the circle `ℝ ⧸ ℤ` has none). Total disconnectedness is used only
to produce the section; the lift for a given section needs compactness of `G` alone.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.7).
* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Prop. 2.2.2 and Cor. 7.2.5.
* H. Koch, *Galois Theory of p-Extensions*, Thm. 3.14.
-/

public section

namespace TauCeti.ContCohomology

open Subgroup (inverseConjugationHom inverseConjugationHom_apply)

universe u v

section Algebra

variable {K : Type u} [Group K] {A : Type v} [AddCommGroup A] [DistribMulAction K A]

/-- Conjugating the argument of a `1`-cocycle by `k` changes its value, after the action of `k`,
by the coboundary of `c k`. -/
theorem smul_apply_inv_mul_mul_of_isCocycle₁ {c : K → A} (hc : groupCohomology.IsCocycle₁ c)
    (k m : K) : k • c (k⁻¹ * m * k) = m • c k - c k + c m := by
  have h := hc k (k⁻¹ * m * k)
  rw [show k * (k⁻¹ * m * k) = m * k by group, hc m k] at h
  rw [eq_sub_of_add_eq h.symm]
  abel

end Algebra

section Lift

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  {N : Subgroup G} [N.Normal]

/-- A **transgression lift** of a function `c : N → M` is a continuous cochain `f : G → M`
satisfying the two identities that make its coboundary descend to `G ⧸ N`:

* `f (g * n) = f g + g • c n`, so `f` extends `c` along right `N`-translation;
* `g • c (g⁻¹ n g) - c n = n • f g - f g`, so `f g` trivialises the difference between `c` and
  its conjugate by `g`.

For a continuous `1`-cocycle `c` on `N` whose class is invariant under conjugation, such lifts
exist when `G` is profinite and `N` is closed (`TauCeti.ContCohomology.transgressionLift`), and
the class of the descended coboundary `TauCeti.ContCohomology.IsTransgressionLift.cocycle` is the
transgression of the class of `c`. -/
structure IsTransgressionLift (c : N → M) (f : G → M) : Prop where
  continuous : Continuous f
  apply_mul : ∀ (g : G) (n : N), f (g * n) = f g + g • c n
  smul_conj_sub : ∀ (g : G) (n : N),
    g • c (inverseConjugationHom N g n) - c n = d0 N M (f g) n

namespace IsTransgressionLift

variable {c c' : N → M} {f f' : G → M}

/-- The zero cochain is a transgression lift of the zero function. -/
theorem zero : IsTransgressionLift (0 : N → M) (0 : G → M) where
  continuous := continuous_const
  apply_mul _ _ := by simp
  smul_conj_sub _ _ := by simp [d0_apply]

/-- Transgression lifts add. -/
theorem add [IsTopologicalAddGroup M] (hf : IsTransgressionLift c f)
    (hf' : IsTransgressionLift c' f') :
    IsTransgressionLift (c + c') (f + f') where
  continuous := hf.continuous.add hf'.continuous
  apply_mul g n := by
    simp only [Pi.add_apply, hf.apply_mul, hf'.apply_mul, smul_add]
    abel
  smul_conj_sub g n := by
    simp only [Pi.add_apply, map_add, ← hf.smul_conj_sub, ← hf'.smul_conj_sub, smul_add]
    abel

/-- Transgression lifts subtract. -/
theorem sub [IsTopologicalAddGroup M] (hf : IsTransgressionLift c f)
    (hf' : IsTransgressionLift c' f') :
    IsTransgressionLift (c - c') (f - f') where
  continuous := hf.continuous.sub hf'.continuous
  apply_mul g n := by
    simp only [Pi.sub_apply, hf.apply_mul, hf'.apply_mul, smul_sub]
    abel
  smul_conj_sub g n := by
    simp only [Pi.sub_apply, map_sub, ← hf.smul_conj_sub, ← hf'.smul_conj_sub, smul_sub]
    abel

/-- The coboundary of `m` on `G` is a transgression lift of the coboundary of `m` on `N`. -/
theorem d0 [IsTopologicalAddGroup M] [ContinuousSMul G M] (m : M) :
    IsTransgressionLift (d0 N M m) (d0 G M m) where
  continuous := continuous_d0_apply m
  apply_mul g n := by
    simp only [d0_apply, Subgroup.smul_def, smul_sub, mul_smul]
    abel
  smul_conj_sub g n := by
    simp only [d0_apply, Subgroup.smul_def, smul_sub, inverseConjugationHom_apply, smul_smul]
    rw [show g * (g⁻¹ * (n : G) * g) = n * g by group, mul_smul]
    abel

/-- A continuous `1`-cocycle on `G` is a transgression lift of its restriction to `N`. -/
theorem of_mem_Z1 [IsTopologicalAddGroup M] {c : G → M} (hc : c ∈ Z1 G M) :
    IsTransgressionLift (fun n : N => c n) c where
  continuous := (mem_Z1_iff.1 hc).1
  apply_mul g n := by
    rw [show c (g * n) = g • c n + c g from (mem_Z1_iff.1 hc).2 g n]
    abel
  smul_conj_sub g n := by
    simpa only [inverseConjugationHom_apply] using
      smul_inverseConjugation_apply_sub_eq_d0 G M N ⟨c, hc⟩ g n

/-- The value of a transgression lift at `1` is fixed by `N`. -/
theorem smul_apply_one (hf : IsTransgressionLift c f) (n : N) : n • f 1 = f 1 := by
  have h := hf.smul_conj_sub 1 n
  simp only [one_smul, d0_apply] at h
  rw [show inverseConjugationHom N 1 n = n by ext; simp, sub_self] at h
  exact (sub_eq_zero.1 h.symm)

/-- On `N`, a transgression lift is the lifted function up to the constant `f 1`. -/
theorem apply_coe (hf : IsTransgressionLift c f) (n : N) : f n = f 1 + c n := by
  simpa using hf.apply_mul 1 n

/-- Subtracting its value at `1` from a transgression lift gives a transgression lift of the same
function that vanishes at `1`. -/
theorem sub_apply_one [IsTopologicalAddGroup M] (hf : IsTransgressionLift c f) :
    IsTransgressionLift c fun g => f g - f 1 where
  continuous := hf.continuous.sub continuous_const
  apply_mul g n := by
    rw [hf.apply_mul]
    abel
  smul_conj_sub g n := by
    rw [hf.smul_conj_sub, d0_apply, d0_apply, smul_sub, hf.smul_apply_one n]
    abel

/-- A transgression lift of the zero function is constant on the cosets of `N`. -/
theorem apply_mul_of_zero (hf : IsTransgressionLift (0 : N → M) f) (g : G) (n : N) :
    f (g * n) = f g := by
  simpa using hf.apply_mul g n

/-- A transgression lift of the zero function takes values fixed by `N`. -/
theorem smul_apply_of_zero (hf : IsTransgressionLift (0 : N → M) f) (n : N) (g : G) :
    n • f g = f g := by
  have h := hf.smul_conj_sub g n
  simp only [Pi.zero_apply, smul_zero, sub_self, d0_apply] at h
  exact (sub_eq_zero.1 h.symm)

/-- The coboundary of a transgression lift is unchanged by right `N`-translation of its second
argument. -/
theorem d1_apply_mul_right (hf : IsTransgressionLift c f) (g h : G) (n : N) :
    d1 G M f (g, h * n) = d1 G M f (g, h) := by
  simp only [d1_apply, ← mul_assoc, hf.apply_mul, smul_add, smul_smul]
  abel

/-- The coboundary of a transgression lift is unchanged by right `N`-translation of its first
argument. -/
theorem d1_apply_mul_left (hf : IsTransgressionLift c f) (g h : G) (n : N) :
    d1 G M f (g * n, h) = d1 G M f (g, h) := by
  have hmul : g * n * h = g * h * (inverseConjugationHom N h n : G) := by
    simp [mul_assoc]
  have hconj := hf.smul_conj_sub h n
  rw [d0_apply, Subgroup.smul_def] at hconj
  have hn : (n : G) • f h = f h + h • c (inverseConjugationHom N h n) - c n := by
    rw [add_sub_assoc, hconj]
    abel
  rw [d1_apply, d1_apply, hmul, hf.apply_mul, hf.apply_mul, mul_smul, hn, mul_smul]
  simp only [smul_add, smul_sub]
  abel

/-- The coboundary of a transgression lift is constant, equal to `f 1`, on `N × G`. -/
theorem d1_apply_coe_left (hf : IsTransgressionLift c f) (n : N) (g : G) :
    d1 G M f (n, g) = f 1 := by
  have hmul : (n : G) * g = g * (inverseConjugationHom N g n : G) := by
    simp [← mul_assoc]
  have hconj := hf.smul_conj_sub g n
  rw [d0_apply, Subgroup.smul_def] at hconj
  rw [d1_apply, hmul, hf.apply_mul, hf.apply_coe,
    show g • c (inverseConjugationHom N g n) = c n + ((n : G) • f g - f g) by
      rw [← hconj]
      abel]
  abel

/-- The coboundary of a transgression lift takes values fixed by `N`. -/
theorem smul_d1_apply (hf : IsTransgressionLift c f) (n : N) (g h : G) :
    n • d1 G M f (g, h) = d1 G M f (g, h) := by
  have h2 := congrFun (d2_comp_d1_apply (G := G) (M := M) f) ((n : G), g, h)
  have hmul : (n : G) * g = g * (inverseConjugationHom N g n : G) := by
    simp [← mul_assoc]
  rw [d2_apply, hmul, hf.d1_apply_mul_left, hf.d1_apply_coe_left, hf.d1_apply_coe_left,
    Pi.zero_apply] at h2
  rw [Subgroup.smul_def, ← sub_eq_zero, ← h2]
  abel

end IsTransgressionLift

end Lift

section Cocycle

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {N : Subgroup G} [N.Normal] {c c' : N → M} {f f' : G → M}

namespace IsTransgressionLift

/-- The coboundary of a transgression lift is a continuous `2`-cocycle on `G`. -/
theorem d1_mem_Z2 (hf : IsTransgressionLift c f) : d1 G M f ∈ Z2 G M :=
  B2_le_Z2 G M (mem_B2_iff.2 ⟨f, hf.continuous, rfl⟩)

/-- The **descended coboundary** of a transgression lift `f`: the continuous `2`-cocycle on
`G ⧸ N` with values in `M ^ N` whose value at `(g N, h N)` is `d¹ f (g, h)`. -/
def cocycle (hf : IsTransgressionLift c f) : Z2 (G ⧸ N) (FixedPoints.addSubgroup N M) :=
  descendZ2 ⟨d1 G M f, hf.d1_mem_Z2⟩
    (fun g h n n' => by
      simp only [hf.d1_apply_mul_right, hf.d1_apply_mul_left])
    (fun n g h => hf.smul_d1_apply n g h)

/-- The descended coboundary evaluates on quotient representatives as the coboundary of the
lift. -/
@[simp]
theorem coe_cocycle_apply_mk (hf : IsTransgressionLift c f) (g h : G) :
    ((hf.cocycle : (G ⧸ N) × (G ⧸ N) → FixedPoints.addSubgroup N M) (g, h) : M) =
      d1 G M f (g, h) :=
  coe_descendZ2_apply_mk _ _ _ g h

/-- The descended coboundary is additive in the lift. -/
theorem cocycle_add (hf : IsTransgressionLift c f) (hf' : IsTransgressionLift c' f') :
    (hf.add hf').cocycle = hf.cocycle + hf'.cocycle := by
  refine Subtype.ext (funext fun p => ?_)
  obtain ⟨q, r⟩ := p
  induction q using QuotientGroup.induction_on with | H g => ?_
  induction r using QuotientGroup.induction_on with | H k => ?_
  refine Subtype.ext ?_
  simp only [AddSubgroup.coe_add, Pi.add_apply, coe_cocycle_apply_mk, map_add]

/-- A lift whose coboundary vanishes descends to the zero cocycle. -/
theorem cocycle_eq_zero (hf : IsTransgressionLift c f) (h : d1 G M f = 0) : hf.cocycle = 0 := by
  refine Subtype.ext (funext fun p => ?_)
  obtain ⟨q, r⟩ := p
  induction q using QuotientGroup.induction_on with | H g => ?_
  induction r using QuotientGroup.induction_on with | H k => ?_
  refine Subtype.ext ?_
  rw [coe_cocycle_apply_mk, h]
  simp

/-- **Independence of the lift.** If `c` and `c'` differ by a `1`-coboundary on `N`, the
descended coboundaries of any of their transgression lifts differ by a `2`-coboundary on
`G ⧸ N`. The primitive is the difference of the two lifts, corrected by the coboundary on `G` of
the element trivialising `c - c'`; it is constant on the cosets of `N` and `N`-invariant, so it
descends to `G ⧸ N`. -/
theorem cocycle_sub_mem_B2 (hf : IsTransgressionLift c f) (hf' : IsTransgressionLift c' f')
    (hcc' : c - c' ∈ B1 N M) :
    (hf.cocycle : (G ⧸ N) × (G ⧸ N) → FixedPoints.addSubgroup N M) - hf'.cocycle ∈
      B2 (G ⧸ N) (FixedPoints.addSubgroup N M) := by
  obtain ⟨m, hm⟩ := mem_B1_iff.1 hcc'
  have hc : c - c' - ContCohomology.d0 N M m = 0 :=
    funext fun n => by simp [d0_apply, ← hm n]
  set e : G → M := f - f' - ContCohomology.d0 G M m with he_def
  have he : IsTransgressionLift (0 : N → M) e := hc ▸ (hf.sub hf').sub (d0 m)
  have hmem : ∀ g : G, e g ∈ FixedPoints.addSubgroup N M := fun g =>
    (FixedPoints.mem_addSubgroup N M _).2 fun n => he.smul_apply_of_zero n g
  have hrel : ∀ a b : G, QuotientGroup.leftRel N a b →
      (⟨e a, hmem a⟩ : FixedPoints.addSubgroup N M) = ⟨e b, hmem b⟩ := fun a b hab =>
    Subtype.ext <| by
      simpa using (he.apply_mul_of_zero a ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.1 hab⟩).symm
  have hd1 : d1 G M f - d1 G M f' = d1 G M e := by
    rw [he_def, map_sub, map_sub, d1_comp_d0_apply, sub_zero]
  refine mem_B2_iff.2 ⟨fun q => Quotient.liftOn' q (fun g => ⟨e g, hmem g⟩) hrel,
    (he.continuous.subtype_mk hmem).quotient_liftOn' hrel, funext fun p => ?_⟩
  obtain ⟨q, r⟩ := p
  induction q using QuotientGroup.induction_on with | H g => ?_
  induction r using QuotientGroup.induction_on with | H k => ?_
  refine Subtype.ext ?_
  rw [Pi.sub_apply, AddSubgroup.coe_sub, coe_cocycle_apply_mk, coe_cocycle_apply_mk,
    ← Pi.sub_apply (d1 G M f), hd1, d1_apply, d1_apply, ← QuotientGroup.mk_mul]
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_sub, coe_quotient_smul_fixedPoints_addSubgroup,
    coe_smul_fixedPoints_addSubgroup, Quotient.liftOn'_mk'']

variable [hquot : ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]

omit hquot in
/-- If `c` and `c'` differ by a `1`-coboundary on `N`, any of their transgression lifts have
the same class in `H²(G ⧸ N, M ^ N)`. -/
theorem mk_cocycle_eq
    (hf : IsTransgressionLift c f) (hf' : IsTransgressionLift c' f')
    (hcc' : c - c' ∈ B1 N M) :
    (hf.cocycle : H2 (G ⧸ N) (FixedPoints.addSubgroup N M)) = hf'.cocycle :=
  H2pi_eq_iff.2 (cocycle_sub_mem_B2 hf hf' hcc')

/-- Inflation kills the class of a descended coboundary: its inflation is the class of the
coboundary of a continuous cochain on `G`. -/
theorem explicitInfl2_mk_cocycle (hf : IsTransgressionLift c f) :
    explicitInfl2 G M N (hf.cocycle : H2 (G ⧸ N) (FixedPoints.addSubgroup N M)) = 0 := by
  rw [cocycle, explicitInfl2_descendZ2, H2pi_eq_zero_iff]
  exact mem_B2_iff.2 ⟨f, hf.continuous, rfl⟩

end IsTransgressionLift

end Cocycle

section Existence

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] {N : Subgroup G} [N.Normal]

/-- **A continuous choice of conjugation primitives.** Let `N` be a closed normal subgroup of a
compact group and `c : N → M` a continuous function to a discrete module such that, for each `g`,
the difference between the conjugate `n ↦ g • c (g⁻¹ n g)` and `c` is the coboundary of some
element. Then those elements can be chosen to depend continuously on `g`.

The conjugate depends on `g` only through a coset of a single open subgroup, by uniform local
constancy of `(n, g) ↦ g • c (g⁻¹ n g)` on the compact group `N × G`; a choice made on the
finitely many cosets is continuous. -/
theorem exists_continuous_smul_conj_sub_eq_d0 (hN : IsClosed (N : Set G)) {c : N → M}
    (hc : Continuous c)
    (h : ∀ g : G, ∃ m : M, ∀ n : N,
      g • c (inverseConjugationHom N g n) - c n = ContCohomology.d0 N M m n) :
    ∃ F : G → M, Continuous F ∧ ∀ (g : G) (n : N),
      g • c (inverseConjugationHom N g n) - c n = ContCohomology.d0 N M (F g) n := by
  have : CompactSpace N := isCompact_iff_compactSpace.mp hN.isCompact
  let ψ : N × G → M := fun p => p.2 • c (inverseConjugationHom N p.2 p.1)
  have hconj : Continuous fun p : N × G => inverseConjugationHom N p.2 p.1 :=
    continuous_induced_rng.2 <| by
      simp only [Function.comp_def, inverseConjugationHom_apply]
      fun_prop
  have hloc : IsLocallyConstant ψ :=
    (IsLocallyConstant.iff_continuous ψ).2 (continuous_snd.smul (hc.comp hconj))
  let V : Subgroup G := (rightTranslationStabilizer ψ).comap (MonoidHom.inr N G)
  have hV : IsOpen (V : Set G) :=
    (isOpen_rightTranslationStabilizer hloc).preimage (continuous_const.prodMk continuous_id)
  have hψV : ∀ (x : G) (v : V) (n : N), ψ (n, x * v) = ψ (n, x) := fun x v n => by
    simpa using (mem_rightTranslationStabilizer.1 (Subgroup.mem_comap.1 v.2)) (n, x)
  have : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hV
  choose m hm using h
  refine ⟨fun g => m (g : G ⧸ V).out,
    (continuous_of_discreteTopology (f := fun q : G ⧸ V => m q.out)).comp
      QuotientGroup.continuous_mk, fun g n => ?_⟩
  have hx : (g : G ⧸ V).out⁻¹ * g ∈ V := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  have hψ := hψV (g : G ⧸ V).out ⟨_, hx⟩ n
  simp only [mul_inv_cancel_left] at hψ
  beta_reduce
  rw [← hm _ n]
  exact congrArg (· - c n) hψ

end Existence

section SectionOffset

variable {G : Type u} [Group G] {N : Subgroup G}
  (s : G ⧸ N → G) (hs : ∀ q, (s q : G ⧸ N) = q)

/-- The element `(s (g N))⁻¹ * g` of `N`, measuring how far `g` is from the chosen representative
of its coset. -/
private def sectionOffset (g : G) : N :=
  ⟨(s g)⁻¹ * g, QuotientGroup.eq.1 (hs g)⟩

private theorem mul_sectionOffset (g : G) : s g * (sectionOffset s hs g : G) = g := by
  simp [sectionOffset]

private theorem sectionOffset_mul (g : G) (n : N) :
    sectionOffset s hs (g * n) = sectionOffset s hs g * n :=
  Subtype.ext (by simp [sectionOffset, QuotientGroup.mk_mul_of_mem g n.2, mul_assoc])

end SectionOffset

section SectionLift

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] {N : Subgroup G} [N.Normal]

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- If the conjugate of `c` by `t` differs from `c` by the coboundary of `A`, then the conjugate
by `t * k`, for `k ∈ N`, differs from `c` by the coboundary of `A + t • c k`. -/
private theorem smul_conj_sub_mul {c : N → M} (hc : groupCohomology.IsCocycle₁ c) {t : G}
    {A : M} (hA : ∀ n : N, t • c (inverseConjugationHom N t n) - c n = d0 N M A n) (k n : N) :
    (t * k) • c (inverseConjugationHom N (t * k) n) - c n = d0 N M (A + t • c k) n := by
  have hconj : inverseConjugationHom N (t * k) n = k⁻¹ * inverseConjugationHom N t n * k :=
    Subtype.ext (by simp [mul_assoc])
  have hA' := hA n
  rw [d0_apply, Subgroup.smul_def] at hA'
  have hk : t • ((inverseConjugationHom N t n) • c k) = (n : G) • t • c k := by
    rw [Subgroup.smul_def, smul_smul, smul_smul, inverseConjugationHom_apply]
    congr 1
    group
  rw [hconj, mul_smul, ← Subgroup.smul_def, smul_apply_inv_mul_mul_of_isCocycle₁ hc, smul_add,
    smul_sub, hk,
    show t • c (inverseConjugationHom N t n) = c n + ((n : G) • A - A) by
      rw [← hA']
      abel,
    d0_apply, Subgroup.smul_def, smul_add]
  abel

variable (s : G ⧸ N → G) (hs : ∀ q, (s q : G ⧸ N) = q)

/-- The unnormalised lift attached to a section `s` and conjugation primitives `F`:
`g ↦ F (s (g N)) + s (g N) • c ((s (g N))⁻¹ * g)`. -/
private def sectionLift (F : G → M) (c : N → M) (g : G) : M :=
  F (s g) + s g • c (sectionOffset s hs g)

private theorem isTransgressionLift_sectionLift (hs_cont : Continuous s) {c : N → M}
    (hc : c ∈ Z1 N M) {F : G → M} (hF : Continuous F)
    (hFc : ∀ (g : G) (n : N), g • c (inverseConjugationHom N g n) - c n = d0 N M (F g) n) :
    IsTransgressionLift c (sectionLift s hs F c) where
  continuous := by
    have hsq : Continuous fun g : G => s g := hs_cont.comp QuotientGroup.continuous_mk
    have hoff : Continuous (sectionOffset s hs) :=
      continuous_induced_rng.2 (hsq.inv.mul continuous_id)
    exact (hF.comp hsq).add (hsq.smul ((mem_Z1_iff.1 hc).1.comp hoff))
  apply_mul g n := by
    simp only [sectionLift, sectionOffset_mul, QuotientGroup.mk_mul_of_mem g n.2,
      (mem_Z1_iff.1 hc).2 (sectionOffset s hs g) n, smul_add, Subgroup.smul_def, smul_smul,
      mul_sectionOffset]
    abel
  smul_conj_sub g n := by
    have h := smul_conj_sub_mul (mem_Z1_iff.1 hc).2 (hFc (s g)) (sectionOffset s hs g) n
    rwa [mul_sectionOffset] at h

end SectionLift

section Transgression

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal]

/-- The chosen continuous conjugation primitives for a cocycle with invariant class. -/
private noncomputable def conjPrimitive (hN : IsClosed (N : Set G)) (c : Z1 N M)
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) : G → M :=
  (exists_continuous_smul_conj_sub_eq_d0 hN (mem_Z1_iff.1 c.2).1
    (exists_smul_conj_sub_eq_d0_of_mem_H1ConjInvariants hc)).choose

private theorem conjPrimitive_spec (hN : IsClosed (N : Set G)) (c : Z1 N M)
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) :
    Continuous (conjPrimitive G M N hN c hc) ∧ ∀ (g : G) (n : N),
      g • (c : N → M) (inverseConjugationHom N g n) - (c : N → M) n =
        d0 N M (conjPrimitive G M N hN c hc g) n :=
  (exists_continuous_smul_conj_sub_eq_d0 hN (mem_Z1_iff.1 c.2).1
    (exists_smul_conj_sub_eq_d0_of_mem_H1ConjInvariants hc)).choose_spec

private theorem isTransgressionLift_sectionLift_conjPrimitive (hN : IsClosed (N : Set G))
    (s : G ⧸ N → G) (hs_cont : Continuous s) (hs : ∀ q, (s q : G ⧸ N) = q) (c : Z1 N M)
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) :
    IsTransgressionLift (c : N → M) (sectionLift s hs (conjPrimitive G M N hN c hc) c) :=
  isTransgressionLift_sectionLift s hs hs_cont c.2 (conjPrimitive_spec G M N hN c hc).1
    (conjPrimitive_spec G M N hN c hc).2

/-- **The section-dependent lift used by transgression.** Given a continuous section `s` of
`G → G ⧸ N` and a continuous `1`-cocycle `c` on `N` whose class is conjugation-invariant, this
is a continuous `1`-cochain on `G` extending `c` (`transgressionLift_apply_coe`) and satisfying
the identities of `TauCeti.ContCohomology.IsTransgressionLift`, so that its coboundary descends
to `G ⧸ N`. It is `g ↦ F (s (g N)) + s (g N) • c ((s (g N))⁻¹ * g)`, normalised to vanish at
`1`, where `F` is a continuous choice of elements trivialising the conjugates of `c`. -/
noncomputable def transgressionLift (hN : IsClosed (N : Set G)) (s : G ⧸ N → G)
    (hs_cont : Continuous s) (hs : ∀ q, (s q : G ⧸ N) = q) (c : Z1 N M)
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) : C1 G M :=
  ⟨_, mem_C1_iff.2 (isTransgressionLift_sectionLift_conjPrimitive G M N hN s hs_cont hs c
    hc).sub_apply_one.continuous⟩

/-- The section-dependent lift is a transgression lift of `c`. -/
theorem isTransgressionLift_transgressionLift (hN : IsClosed (N : Set G)) (s : G ⧸ N → G)
    (hs_cont : Continuous s) (hs : ∀ q, (s q : G ⧸ N) = q) (c : Z1 N M)
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) :
    IsTransgressionLift (c : N → M) (transgressionLift G M N hN s hs_cont hs c hc) :=
  (isTransgressionLift_sectionLift_conjPrimitive G M N hN s hs_cont hs c hc).sub_apply_one

/-- The section-dependent lift vanishes at `1`. -/
@[simp]
theorem transgressionLift_apply_one (hN : IsClosed (N : Set G)) (s : G ⧸ N → G)
    (hs_cont : Continuous s) (hs : ∀ q, (s q : G ⧸ N) = q) (c : Z1 N M)
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) :
    (transgressionLift G M N hN s hs_cont hs c hc : G → M) 1 = 0 :=
  sub_self _

/-- The section-dependent lift extends `c`. -/
@[simp]
theorem transgressionLift_apply_coe (hN : IsClosed (N : Set G)) (s : G ⧸ N → G)
    (hs_cont : Continuous s) (hs : ∀ q, (s q : G ⧸ N) = q) (c : Z1 N M)
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) (n : N) :
    (transgressionLift G M N hN s hs_cont hs c hc : G → M) n = (c : N → M) n := by
  rw [(isTransgressionLift_transgressionLift G M N hN s hs_cont hs c hc).apply_coe,
    transgressionLift_apply_one, zero_add]

/-- **The raw transgression `2`-cochain**, obtained by differentiating `transgressionLift` and
descending to `G ⧸ N`, with values in `M ^ N`. -/
noncomputable def transgressionCochain (hN : IsClosed (N : Set G)) (s : G ⧸ N → G)
    (hs_cont : Continuous s) (hs : ∀ q, (s q : G ⧸ N) = q) (c : Z1 N M)
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) :
    C2 (G ⧸ N) (FixedPoints.addSubgroup N M) :=
  ⟨_, Z2_le_C2 _ _ (isTransgressionLift_transgressionLift G M N hN s hs_cont hs c hc).cocycle.2⟩

/-- **The lift-and-differentiate formula.** After the inclusion `M ^ N ↪ M`, the raw
transgression at `(q, r)` is `d¹` of the lift at the chosen representatives `(s q, s r)`. -/
theorem transgressionCochain_apply (hN : IsClosed (N : Set G)) (s : G ⧸ N → G)
    (hs_cont : Continuous s) (hs : ∀ q, (s q : G ⧸ N) = q) (c : Z1 N M)
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) (q r : G ⧸ N) :
    (((transgressionCochain G M N hN s hs_cont hs c hc : (G ⧸ N) × (G ⧸ N) →
        FixedPoints.addSubgroup N M) (q, r)) : M) =
      d1 G M (transgressionLift G M N hN s hs_cont hs c hc) (s q, s r) := by
  conv_lhs => rw [← hs q, ← hs r]
  exact IsTransgressionLift.coe_cocycle_apply_mk _ (s q) (s r)

/-- The raw transgression is a continuous `2`-cocycle. -/
theorem transgressionCochain_isCocycle (hN : IsClosed (N : Set G)) (s : G ⧸ N → G)
    (hs_cont : Continuous s) (hs : ∀ q, (s q : G ⧸ N) = q) (c : Z1 N M)
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) :
    (transgressionCochain G M N hN s hs_cont hs c hc : (G ⧸ N) × (G ⧸ N) →
      FixedPoints.addSubgroup N M) ∈ Z2 (G ⧸ N) (FixedPoints.addSubgroup N M) :=
  (isTransgressionLift_transgressionLift G M N hN s hs_cont hs c hc).cocycle.2

/-- The raw transgression bundled as a continuous `2`-cocycle. -/
noncomputable def transgressionCocycle (hN : IsClosed (N : Set G)) (s : G ⧸ N → G)
    (hs_cont : Continuous s) (hs : ∀ q, (s q : G ⧸ N) = q) (c : Z1 N M)
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) :
    Z2 (G ⧸ N) (FixedPoints.addSubgroup N M) :=
  ⟨_, transgressionCochain_isCocycle G M N hN s hs_cont hs c hc⟩

/-- The bundled raw transgression is the descended coboundary of the section-dependent lift. -/
private theorem transgressionCocycle_eq_cocycle (hN : IsClosed (N : Set G)) (s : G ⧸ N → G)
    (hs_cont : Continuous s) (hs : ∀ q, (s q : G ⧸ N) = q) (c : Z1 N M)
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) :
    transgressionCocycle G M N hN s hs_cont hs c hc =
      (isTransgressionLift_transgressionLift G M N hN s hs_cont hs c hc).cocycle :=
  rfl

/-- **Change of section and of representative is an explicit coboundary.** The raw
transgressions for two continuous sections and two cohomologous representatives differ by a
continuous `2`-coboundary on `G ⧸ N`. -/
theorem transgressionCochain_sub_mem_B2 (hN : IsClosed (N : Set G)) (s s' : G ⧸ N → G)
    (hs_cont : Continuous s) (hs'_cont : Continuous s') (hs : ∀ q, (s q : G ⧸ N) = q)
    (hs' : ∀ q, (s' q : G ⧸ N) = q) (c c' : Z1 N M)
    (hc : (c : H1 N M) ∈ H1ConjInvariants G M N) (hc' : (c' : H1 N M) ∈ H1ConjInvariants G M N)
    (hcc' : (c : H1 N M) = c') :
    (transgressionCochain G M N hN s hs_cont hs c hc : (G ⧸ N) × (G ⧸ N) →
        FixedPoints.addSubgroup N M) -
      transgressionCochain G M N hN s' hs'_cont hs' c' hc' ∈
      B2 (G ⧸ N) (FixedPoints.addSubgroup N M) :=
  IsTransgressionLift.cocycle_sub_mem_B2 _ _ (H1pi_eq_iff.1 hcc')

variable [TotallyDisconnectedSpace G] [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]

/-- **The transgression** `tg : H¹(N, M)^{G ⧸ N} → H²(G ⧸ N, M ^ N)` for a closed normal
subgroup `N` of a profinite group `G` and a discrete module `M`: lift a representative cocycle
through a continuous section of `G → G ⧸ N`, differentiate, and descend to `G ⧸ N`. The class
depends neither on the section nor on the representative (`transgression_apply`). -/
noncomputable def transgression (hN : IsClosed (N : Set G)) :
    H1ConjInvariants G M N →+ H2 (G ⧸ N) (FixedPoints.addSubgroup N M) where
  toFun y := (transgressionCocycle G M N hN (exists_continuous_section N hN).choose
    (exists_continuous_section N hN).choose_spec.1 (exists_continuous_section N hN).choose_spec.2.1
    (QuotientAddGroup.mk_surjective (y : H1 N M)).choose
    (by rw [(QuotientAddGroup.mk_surjective (y : H1 N M)).choose_spec]; exact y.2) :
      H2 (G ⧸ N) (FixedPoints.addSubgroup N M))
  map_zero' := by
    rw [transgressionCocycle_eq_cocycle, IsTransgressionLift.mk_cocycle_eq _
      IsTransgressionLift.zero, IsTransgressionLift.cocycle_eq_zero _ (map_zero _),
      QuotientAddGroup.mk_zero]
    rw [sub_zero, ← H1pi_eq_zero_iff, (QuotientAddGroup.mk_surjective _).choose_spec]
    rfl
  map_add' x y := by
    simp only [transgressionCocycle_eq_cocycle]
    rw [IsTransgressionLift.mk_cocycle_eq _
      ((isTransgressionLift_transgressionLift G M N hN _ _ _ _ _).add
        (isTransgressionLift_transgressionLift G M N hN _ _ _ _ _)),
      IsTransgressionLift.cocycle_add, QuotientAddGroup.mk_add]
    rw [← AddSubgroup.coe_add, ← H1pi_eq_iff, QuotientAddGroup.mk_add,
      (QuotientAddGroup.mk_surjective _).choose_spec,
      (QuotientAddGroup.mk_surjective _).choose_spec,
      (QuotientAddGroup.mk_surjective _).choose_spec, AddSubgroup.coe_add]

/-- **The transgression is the class of the raw cochain,** for every continuous section and every
representative cocycle. -/
theorem transgression_apply (hN : IsClosed (N : Set G)) (s : G ⧸ N → G)
    (hs_cont : Continuous s) (hs : ∀ q, (s q : G ⧸ N) = q) (y : H1ConjInvariants G M N)
    (c : Z1 N M) (hc : (c : H1 N M) = y) :
    transgression G M N hN y =
      (transgressionCocycle G M N hN s hs_cont hs c (hc ▸ y.2) :
        H2 (G ⧸ N) (FixedPoints.addSubgroup N M)) :=
  H2pi_eq_iff.2 (transgressionCochain_sub_mem_B2 G M N hN _ s _ hs_cont _ hs _ c _ _
    ((QuotientAddGroup.mk_surjective _).choose_spec.trans hc.symm))

/-- **Transgression kills restriction.** The transgression of the restriction of a class in
`H¹(G, M)` vanishes: a cocycle on `G` is itself a transgression lift of its restriction, and its
coboundary is zero. -/
theorem transgression_explicitResConj1 (hN : IsClosed (N : Set G)) (x : H1 G M) :
    transgression G M N hN (explicitResConj1 G M N x) = 0 := by
  obtain ⟨s, hs_cont, hs, -⟩ := exists_continuous_section N hN
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    set c' := cocyclesMap1 G M N M (ContinuousMonoidHom.subgroupSubtype N) (AddMonoidHom.id M)
      continuous_id (id_subgroupSubtype_smul G M N) c
    rw [transgression_apply G M N hN s hs_cont hs _ c'
        ((explicitRes1_mk G M N c).symm.trans (coe_explicitResConj1 G M N _).symm),
      transgressionCocycle_eq_cocycle, IsTransgressionLift.mk_cocycle_eq _
        (IsTransgressionLift.of_mem_Z1 (N := N) c.2) ?_,
      IsTransgressionLift.cocycle_eq_zero _ (d1_apply_eq_zero_iff.2 (mem_Z1_iff.1 c.2).2),
      QuotientAddGroup.mk_zero]
    have hc' : (c' : N → M) = fun n : N => (c : G → M) n := funext fun n => by simp [c']
    rw [hc', sub_self]
    exact zero_mem _

/-- **Inflation kills transgression.** The inflation to `H²(G, M)` of a transgressed class
vanishes: it is the class of the coboundary of a continuous cochain on `G`. -/
theorem explicitInfl2_transgression (hN : IsClosed (N : Set G)) (y : H1ConjInvariants G M N) :
    explicitInfl2 G M N (transgression G M N hN y) = 0 := by
  obtain ⟨s, hs_cont, hs, -⟩ := exists_continuous_section N hN
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective (y : H1 N M)
  rw [transgression_apply G M N hN s hs_cont hs y c hc, transgressionCocycle_eq_cocycle]
  exact IsTransgressionLift.explicitInfl2_mk_cocycle _

end Transgression

end TauCeti.ContCohomology

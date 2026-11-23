/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.Topology.Algebra.Group.Connected

import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle.Topology

/-!
# Locally continuous cohomology in degrees one and two

A projective unitary representation of a topological group `G` has a multiplier `ω` with
`U g * U h = ω (g, h) • U (g * h)` that can in general only be chosen continuous *near the
identity*, not everywhere: already the projection `U(2) → PU(2) ≅ SO(3)` has no continuous
section. The cohomology that classifies such multipliers, and with them the central extensions of
`G` that are locally trivial bundles, is the *locally continuous* cohomology of Neeb and of
Wagemann–Wockel. This file builds it in degrees
`1` and `2` on the explicit complex of `TauCeti/RepresentationTheory/Homological/ContCohomology/
LowDegree.lean`, for a topological group `G` acting on a commutative topological group `M`.

A `1`-cochain `b : G → M` is *locally continuous* when it is continuous at every point of some
neighbourhood of `1` (`TauCeti.ContCohomology.LC1`). A `2`-cochain `f : G × G → M` is locally
continuous (`TauCeti.ContCohomology.LC2`) when it is continuous near `(1, 1)` and, for every `g`,
its *conjugation cochain* `h ↦ f (g, h) - f (g * h * g⁻¹, g)` is continuous near `1`
(`TauCeti.ContCohomology.conjugationCochain`). The second condition is the one that makes
conjugation by a lift of `g` continuous in the extension: in the twisted product of `f`, the
section `σ` satisfies `σ g * σ h * (σ g)⁻¹ = c_g(h) * σ (g * h * g⁻¹)`, where `c_g` is that cochain.
The coboundaries `B²_lc` are the images under `d¹` of the locally continuous `1`-cochains, and
`H²_lc(G, M) = Z²_lc / B²_lc` (`TauCeti.ContCohomology.LCH2`).

In degree one no new group is needed: a `1`-cocycle continuous at `1` is continuous
(`groupCohomology.IsCocycle₁.continuous_of_continuousAt_one`), so the locally continuous
`1`-cocycles are exactly the continuous ones (`TauCeti.ContCohomology.mem_Z1_iff_continuousAt_one`)
and `H¹_lc(G, M)` is the continuous `H¹(G, M)` of `TauCeti.ContCohomology.H1`. For a trivial action
the principal crossed homomorphisms vanish, and this is the group of continuous characters.

## Main definitions

* `TauCeti.ContCohomology.LC1`: the `1`-cochains continuous near `1`.
* `TauCeti.ContCohomology.conjugationCochain`: the conjugation cochain of a `2`-cochain at `g`.
* `TauCeti.ContCohomology.LC2`: the locally continuous `2`-cochains.
* `TauCeti.ContCohomology.LCZ2`, `TauCeti.ContCohomology.LCB2`: the locally continuous
  `2`-cocycles and the coboundaries of locally continuous `1`-cochains.
* `TauCeti.ContCohomology.LCH2`: the locally continuous cohomology group `H²_lc(G, M)`, with class
  map `TauCeti.ContCohomology.LCH2pi`, and `TauCeti.ContCohomology.H2ToLCH2`, the comparison map
  from continuous cohomology.

## Main results

* `TauCeti.ContCohomology.d1_mem_LC2`: the coboundary of a locally continuous `1`-cochain is a
  locally continuous `2`-cochain, so `B²_lc ≤ Z²_lc` (`TauCeti.ContCohomology.LCB2_le_LCZ2`).
* `TauCeti.ContCohomology.conjugationCochain_mul`: the conjugation cochain of a `2`-cocycle at a
  product `a * b` is `a • c_b + c_a ∘ (conjugation by b)` plus a coboundary term.
* `TauCeti.ContCohomology.conjugationCochain_mem_LC1_of_preconnected` and
  `TauCeti.ContCohomology.mem_LCZ2_iff_of_preconnected`: for a connected group the conjugation
  condition is automatic, so a `2`-cocycle is locally continuous as soon as it is continuous near
  `(1, 1)`.
* `TauCeti.ContCohomology.LCZ2_eq_ker_d2`: over a discrete group every `2`-cocycle is locally
  continuous.
* `TauCeti.ContCohomology.mem_Z1_iff_continuousAt_one`: a `1`-cocycle is continuous exactly when it
  is continuous at `1`.

## References

* K.-H. Neeb, *Abelian extensions of infinite-dimensional Lie groups*, Travaux mathématiques 15
  (2004), 69–194, Proposition II.6 and the computation before it, read with continuous in place
  of smooth.
* F. Wagemann, C. Wockel, *A cocycle model for topological and Lie group cohomology*,
  Trans. Amer. Math. Soc. 367 (2015), 1871–1909, Remarks I.3 and I.4.
-/

public section

namespace TauCeti.ContCohomology

open Filter Topology groupCohomology

universe u v

/-! ### Locally continuous `1`-cochains -/

section LC1

variable (G : Type u) [TopologicalSpace G] [One G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- The **locally continuous `1`-cochains**: the functions `G → M` that are continuous at every
point of some neighbourhood of `1`. -/
def LC1 : AddSubgroup (G → M) where
  carrier := {f | ∀ᶠ g in 𝓝 1, ContinuousAt f g}
  zero_mem' := Eventually.of_forall fun _ => continuousAt_const
  add_mem' hf hf' := (hf.and hf').mono fun _ h => h.1.add h.2
  neg_mem' hf := hf.mono fun _ h => h.neg

variable {G M}

/-- Membership in `LC1` is continuity at every point near `1`. -/
@[simp]
theorem mem_LC1_iff {f : G → M} : f ∈ LC1 G M ↔ ∀ᶠ g in 𝓝 1, ContinuousAt f g := (Iff.rfl)

variable (G M)

/-- Continuous cochains are locally continuous. -/
theorem C1_le_LC1 : C1 G M ≤ LC1 G M := fun _ hf =>
  Eventually.of_forall fun _ => (mem_C1_iff.1 hf).continuousAt

/-- Over a discrete group every `1`-cochain is locally continuous. -/
@[simp]
theorem LC1_eq_top [DiscreteTopology G] : LC1 G M = ⊤ :=
  top_le_iff.1 (C1_eq_top (G := G) (M := M) ▸ C1_le_LC1 G M)

end LC1

section LC1Conj

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- Precomposing a locally continuous `1`-cochain with conjugation by `g` keeps it locally
continuous. -/
theorem comp_conj_mem_LC1 {b : G → M} (hb : b ∈ LC1 G M) (g : G) :
    (fun h => b (g * h * g⁻¹)) ∈ LC1 G M := by
  have hconj : Tendsto (fun h : G => g * h * g⁻¹) (𝓝 1) (𝓝 1) := by
    simpa using (IsTopologicalGroup.continuous_conj g).tendsto 1
  filter_upwards [hconj.eventually (mem_LC1_iff.1 hb)] with h hh
  exact hh.comp (f := fun k : G => g * k * g⁻¹) (IsTopologicalGroup.continuous_conj g).continuousAt

end LC1Conj

/-! ### Locally continuous `2`-cochains -/

section ConjugationCochain

variable (G : Type u) [Group G] (M : Type v) [AddCommGroup M]

/-- The **conjugation cochain** `h ↦ f (g, h) - f (g * h * g⁻¹, g)` of a `2`-cochain `f` at `g`.
For a cocycle it measures the conjugation by the canonical lift of `g` in the twisted product of
`f`: there `σ g * σ h * (σ g)⁻¹` is `σ (g * h * g⁻¹)` translated by this value. -/
def conjugationCochain (g : G) : (G × G → M) →+ (G → M) where
  toFun f h := f (g, h) - f (g * h * g⁻¹, g)
  map_zero' := by ext; simp
  map_add' f f' := by ext; simp only [Pi.add_apply]; abel

variable {G M}

@[simp]
theorem conjugationCochain_apply (f : G × G → M) (g h : G) :
    conjugationCochain G M g f h = f (g, h) - f (g * h * g⁻¹, g) :=
  (rfl)

end ConjugationCochain

section LC2

variable (G : Type u) [Group G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- The **locally continuous `2`-cochains**: the functions `f : G × G → M` that are continuous at
every point of some neighbourhood of `(1, 1)` and whose conjugation cochain at every `g` is
continuous at every point of some neighbourhood of `1`. -/
def LC2 : AddSubgroup (G × G → M) :=
  LC1 (G × G) M ⊓ ⨅ g : G, (LC1 G M).comap (conjugationCochain G M g)

variable {G M}

/-- Membership in `LC2`: continuity near `(1, 1)` and the conjugation condition at every `g`. -/
theorem mem_LC2_iff {f : G × G → M} :
    f ∈ LC2 G M ↔ f ∈ LC1 (G × G) M ∧ ∀ g : G, conjugationCochain G M g f ∈ LC1 G M := by
  simp only [LC2, AddSubgroup.mem_inf, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]

/-- Membership in `LC2`, with both conditions spelled out as continuity near the identity. -/
theorem mem_LC2_iff' {f : G × G → M} :
    f ∈ LC2 G M ↔ (∀ᶠ p in 𝓝 1, ContinuousAt f p) ∧
      ∀ g : G, ∀ᶠ h in 𝓝 1, ContinuousAt (fun k => f (g, k) - f (g * k * g⁻¹, g)) h :=
  mem_LC2_iff

/-- The conjugation cochain of a `2`-cochain continuous on a neighbourhood of `(1, 1)` is
continuous near `1`, at every `g` close enough to `1`. This is the part of the conjugation
condition that continuity near the identity already gives. -/
theorem eventually_conjugationCochain_mem_LC1 [IsTopologicalGroup G] {f : G × G → M}
    (hf : f ∈ LC1 (G × G) M) : ∀ᶠ g in 𝓝 1, conjugationCochain G M g f ∈ LC1 G M := by
  have hφ : Tendsto (fun p : G × G => (p.1 * p.2 * p.1⁻¹, p.1)) (𝓝 1) (𝓝 1) := by
    have hc : Continuous fun p : G × G => (p.1 * p.2 * p.1⁻¹, p.1) := by fun_prop
    exact hc.tendsto' 1 1 (by simp)
  have hpair : ∀ᶠ p : G × G in 𝓝 1 ×ˢ 𝓝 1,
      ContinuousAt f p ∧ ContinuousAt f (p.1 * p.2 * p.1⁻¹, p.1) :=
    nhds_prod_eq (x := (1 : G)) (y := (1 : G)) ▸ (mem_LC1_iff.1 hf).and (hφ.eventually hf)
  filter_upwards [hpair.curry] with g hg
  filter_upwards [hg] with h hh
  exact (hh.1.comp (f := fun k : G => (g, k)) (continuousAt_const.prodMk continuousAt_id)).sub
    (hh.2.comp (f := fun k : G => (g * k * g⁻¹, g))
      (((IsTopologicalGroup.continuous_conj g).continuousAt).prodMk continuousAt_const))

variable (G M)

/-- Continuous `2`-cochains are locally continuous. -/
theorem C2_le_LC2 [IsTopologicalGroup G] : C2 G M ≤ LC2 G M := by
  intro f hf
  have hc : Continuous f := mem_C2_iff.1 hf
  refine mem_LC2_iff.2 ⟨C1_le_LC1 _ _ (mem_C1_iff.2 hc), fun g => C1_le_LC1 G M (mem_C1_iff.2 ?_)⟩
  have : Continuous fun h : G => f (g, h) - f (g * h * g⁻¹, g) := by fun_prop
  simpa only [← conjugationCochain_apply] using this

/-- Over a discrete group every `2`-cochain is locally continuous. -/
@[simp]
theorem LC2_eq_top [DiscreteTopology G] : LC2 G M = ⊤ := by
  simp [LC2]

end LC2

/-! ### Coboundaries of locally continuous `1`-cochains -/

section Coboundary

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribSMul G M] [ContinuousSMul G M]

/-- **The coboundary of a locally continuous `1`-cochain is locally continuous.** -/
theorem d1_mem_LC2 {b : G → M} (hb : b ∈ LC1 G M) : d1 G M b ∈ LC2 G M := by
  have hb' := mem_LC1_iff.1 hb
  refine mem_LC2_iff.2 ⟨?_, fun g => ?_⟩
  · have h₁ : ∀ᶠ p : G × G in 𝓝 1, ContinuousAt b p.1 := continuousAt_fst.tendsto.eventually hb'
    have h₂ : ∀ᶠ p : G × G in 𝓝 1, ContinuousAt b p.2 := continuousAt_snd.tendsto.eventually hb'
    have h₁₂ : ∀ᶠ p : G × G in 𝓝 1, ContinuousAt b (p.1 * p.2) :=
      (continuous_mul.tendsto' (1 : G × G) 1 (mul_one 1)).eventually hb'
    filter_upwards [h₁, h₂, h₁₂] with p hp₁ hp₂ hp₁₂
    have : ContinuousAt (fun q : G × G => q.1 • b q.2 - b (q.1 * q.2) + b q.1) p :=
      ((continuousAt_fst.smul (hp₂.comp continuousAt_snd)).sub
        (hp₁₂.comp (f := fun q : G × G => q.1 * q.2)
          (continuousAt_fst.mul continuousAt_snd))).add (hp₁.comp continuousAt_fst)
    exact this.congr (Eventually.of_forall fun q => (d1_apply b q.1 q.2).symm)
  · rw [mem_LC1_iff]
    filter_upwards [hb', mem_LC1_iff.1 (comp_conj_mem_LC1 hb g)] with h hh hh'
    have : ContinuousAt
        (fun k : G => g • b k + b g - (g * k * g⁻¹) • b g - b (g * k * g⁻¹)) h :=
      (((hh.const_smul g).add continuousAt_const).sub
        (((IsTopologicalGroup.continuous_conj g).smul continuous_const).continuousAt)).sub hh'
    refine this.congr (Eventually.of_forall fun k => ?_)
    simp only [conjugationCochain_apply, d1_apply, inv_mul_cancel_right]
    abel

end Coboundary

/-! ### The conjugation cochain of a cocycle at a product -/

section ConjugationMul

variable {G : Type u} [Group G] {M : Type v} [AddCommGroup M] [DistribSMul G M]

/-- **The conjugation cochain of a `2`-cocycle at a product.** For a `2`-cocycle `f`,
`c_(a * b) (h) = a • c_b (h) + c_a (b * h * b⁻¹) + (d⁰ (f (a, b))) (a * b * h * (a * b)⁻¹)`, where
`c_g` is `conjugationCochain G M g f`. It is the cochain form of composing conjugations by the lifts
of `b` and of `a` in the twisted product of `f`, the last term correcting the lift of `a * b`. -/
theorem conjugationCochain_mul {f : G × G → M}
    (hf : IsCocycle₂ f) (a b h : G) :
    conjugationCochain G M (a * b) f h =
      a • conjugationCochain G M b f h + conjugationCochain G M a f (b * h * b⁻¹) +
        d0 G M (f (a, b)) (a * b * h * (a * b)⁻¹) := by
  have e₁ := hf a b h
  have e₂ := hf (a * b * h * (a * b)⁻¹) a b
  have e₃ := hf a (b * h * b⁻¹) b
  -- the cocycle identity at `(a, b, h)`, `(a * b * h * (a * b)⁻¹, a, b)` and `(a, b * h * b⁻¹, b)`
  have hl : a * (b * h * b⁻¹) * a⁻¹ = a * b * h * (a * b)⁻¹ := by group
  have hla : a * b * h * (a * b)⁻¹ * a = a * (b * h * b⁻¹) := by group
  have hkb : b * h * b⁻¹ * b = b * h := by group
  rw [hla] at e₂
  rw [hkb] at e₃
  simp only [conjugationCochain_apply, d0_apply, hl, smul_sub]
  rw [eq_sub_of_add_eq e₁, eq_sub_of_add_eq' e₂.symm, eq_sub_of_add_eq e₃.symm]
  abel

end ConjugationMul

/-! ### Locally continuous `2`-cocycles and `H²_lc` -/

section Cocycles

variable (G : Type u) [Group G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribSMul G M]

/-- The **locally continuous `2`-cocycles** `Z²_lc = LC² ⊓ ker d²`. -/
def LCZ2 : AddSubgroup (G × G → M) := LC2 G M ⊓ (d2 G M).ker

/-- The **locally continuous `2`-coboundaries** `B²_lc = d¹(LC¹)`, the image of the locally
continuous `1`-cochains. -/
def LCB2 : AddSubgroup (G × G → M) := (LC1 G M).map (d1 G M)

variable {G M}

/-- A cochain is a locally continuous `2`-cocycle exactly when it is locally continuous and
satisfies the `2`-cocycle identity. -/
@[simp]
theorem mem_LCZ2_iff {f : G × G → M} : f ∈ LCZ2 G M ↔ f ∈ LC2 G M ∧ IsCocycle₂ f :=
  AddSubgroup.mem_inf.trans (and_congr Iff.rfl (AddMonoidHom.mem_ker.trans d2_apply_eq_zero_iff))

/-- Membership in `B²_lc` exhibits a locally continuous primitive. -/
@[simp]
theorem mem_LCB2_iff {f : G × G → M} : f ∈ LCB2 G M ↔ ∃ b ∈ LC1 G M, d1 G M b = f :=
  AddSubgroup.mem_map

variable (G M)

/-- Continuous `2`-coboundaries are locally continuous `2`-coboundaries. -/
theorem B2_le_LCB2 : B2 G M ≤ LCB2 G M := by
  intro f hf
  obtain ⟨b, hb, rfl⟩ := mem_B2_iff.1 hf
  exact mem_LCB2_iff.2 ⟨b, C1_le_LC1 G M (mem_C1_iff.2 hb), rfl⟩

/-- Over a discrete group every `2`-cocycle is locally continuous. -/
theorem LCZ2_eq_ker_d2 [DiscreteTopology G] : LCZ2 G M = (d2 G M).ker := by
  simp [LCZ2]

variable [IsTopologicalGroup G]

/-- Continuous `2`-cocycles are locally continuous `2`-cocycles. -/
theorem Z2_le_LCZ2 : Z2 G M ≤ LCZ2 G M := fun _ hf =>
  mem_LCZ2_iff.2 ⟨C2_le_LC2 G M (Z2_le_C2 G M hf), (mem_Z2_iff.1 hf).2⟩

variable [ContinuousSMul G M] [IsScalarTower G G M]

/-- `d ∘ d = 0` in the form the locally continuous `H²` needs: locally continuous coboundaries are
locally continuous cocycles. -/
theorem LCB2_le_LCZ2 : LCB2 G M ≤ LCZ2 G M := by
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨d1_mem_LC2 hb, d2_comp_d1_apply b⟩

/-- The **locally continuous cohomology group** `H²_lc(G, M) = Z²_lc / B²_lc`. As for
`TauCeti.ContCohomology.H2`, the denominator is `B²_lc` viewed inside `Z²_lc`, and
`TauCeti.ContCohomology.LCB2_le_LCZ2` makes it the whole of `B²_lc`. -/
abbrev LCH2 :=
  let _h := LCB2_le_LCZ2 G M
  (LCZ2 G M) ⧸ ((LCB2 G M).addSubgroupOf (LCZ2 G M))

/-- The class map of locally continuous cohomology in degree `2`. -/
abbrev LCH2pi : (LCZ2 G M) →+ LCH2 G M := QuotientAddGroup.mk' _

variable {G M}

/-- A locally continuous `2`-cocycle has trivial class exactly when it is the coboundary of a
locally continuous `1`-cochain. -/
theorem LCH2pi_eq_zero_iff {f : LCZ2 G M} :
    LCH2pi G M f = 0 ↔ (f : G × G → M) ∈ LCB2 G M := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

omit [IsTopologicalGroup G] [ContinuousSMul G M] [IsScalarTower G G M] in
/-- Two locally continuous `2`-cocycles have the same class exactly when they differ by the
coboundary of a locally continuous `1`-cochain. -/
@[simp]
theorem LCH2pi_eq_iff {f f' : LCZ2 G M} :
    (f : LCH2 G M) = (f' : LCH2 G M) ↔ (f : G × G → M) - f' ∈ LCB2 G M := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub]

end Cocycles

section Comparison

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- The **comparison map** `H²(G, M) → H²_lc(G, M)` from continuous to locally continuous
cohomology, induced by the inclusions `Z² ≤ Z²_lc` and `B² ≤ B²_lc`. -/
def H2ToLCH2 : H2 G M →+ LCH2 G M :=
  QuotientAddGroup.map _ _ (AddSubgroup.inclusion (Z2_le_LCZ2 G M)) fun _ hf =>
    AddSubgroup.mem_addSubgroupOf.2 (B2_le_LCB2 G M (AddSubgroup.mem_addSubgroupOf.1 hf))

variable {G M}

/-- The comparison map sends the class of a continuous cocycle to its locally continuous class. -/
@[simp]
theorem H2ToLCH2_mk (f : Z2 G M) :
    H2ToLCH2 G M (f : H2 G M) = (AddSubgroup.inclusion (Z2_le_LCZ2 G M) f : LCH2 G M) :=
  (rfl)

end Comparison

/-! ### Connected groups -/

section Connected

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribSMul G M] [ContinuousSMul G M]

/-- The elements `g` at which the conjugation cochain of a `2`-cocycle is locally continuous form a
submonoid: at a product it is `TauCeti.ContCohomology.conjugationCochain_mul`, a sum of
locally continuous functions of `h`. -/
private def conjugationSubmonoid {f : G × G → M} (hf : IsCocycle₂ f)
    (hc : f ∈ LC1 (G × G) M) : Submonoid G where
  carrier := {g | conjugationCochain G M g f ∈ LC1 G M}
  one_mem' := (eventually_conjugationCochain_mem_LC1 hc).self_of_nhds
  mul_mem' {a b} ha hb := by
    have hb' : ∀ᶠ h in 𝓝 1, ContinuousAt (conjugationCochain G M b f) h := hb
    refine (mem_LC1_iff (f := conjugationCochain G M (a * b) f)).2 ?_
    filter_upwards [hb', mem_LC1_iff.1 (comp_conj_mem_LC1 ha b)] with h hh hh'
    have : ContinuousAt (fun k : G => a • conjugationCochain G M b f k +
        conjugationCochain G M a f (b * k * b⁻¹) + d0 G M (f (a, b)) (a * b * k * (a * b)⁻¹)) h :=
      ((hh.const_smul a).add hh').add
        ((continuous_d0_apply _).comp (IsTopologicalGroup.continuous_conj (a * b))).continuousAt
    exact this.congr (Eventually.of_forall fun k => (conjugationCochain_mul hf a b k).symm)

/-- **Over a connected group the conjugation condition is automatic.** If a `2`-cocycle is
continuous near `(1, 1)`, then its conjugation cochain at every `g` is continuous near `1`. -/
theorem conjugationCochain_mem_LC1_of_preconnected [PreconnectedSpace G] {f : G × G → M}
    (hf : IsCocycle₂ f) (hc : f ∈ LC1 (G × G) M) (g : G) :
    conjugationCochain G M g f ∈ LC1 G M := by
  have htop : conjugationSubmonoid hf hc = ⊤ :=
    Submonoid.eq_top_of_mem_nhds_one (eventually_conjugationCochain_mem_LC1 hc)
  exact (htop ▸ Submonoid.mem_top g : g ∈ conjugationSubmonoid hf hc)

/-- **Over a connected group a `2`-cocycle is locally continuous as soon as it is continuous near
`(1, 1)`.** -/
theorem mem_LCZ2_iff_of_preconnected [PreconnectedSpace G] {f : G × G → M} :
    f ∈ LCZ2 G M ↔ f ∈ LC1 (G × G) M ∧ IsCocycle₂ f := by
  rw [mem_LCZ2_iff, mem_LC2_iff]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h =>
    ⟨⟨h.1, conjugationCochain_mem_LC1_of_preconnected h.2 h.1⟩, h.2⟩⟩

end Connected

/-! ### Degree one -/

section DegreeOne

variable {G : Type u} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribSMul G M] [ContinuousConstSMul G M]

/-- **The locally continuous `1`-cocycles are the continuous ones.** A `1`-cocycle lies in `Z¹`
exactly when it is continuous at `1`; in particular a `1`-cocycle continuous near `1` is
continuous, so the locally continuous `H¹` is `TauCeti.ContCohomology.H1`. -/
theorem mem_Z1_iff_continuousAt_one {f : G → M} :
    f ∈ Z1 G M ↔ ContinuousAt f 1 ∧ IsCocycle₁ f := by
  rw [mem_Z1_iff]
  exact ⟨fun h => ⟨h.1.continuousAt, h.2⟩,
    fun h => ⟨h.2.continuous_of_continuousAt_one h.1, h.2⟩⟩

end DegreeOne

end TauCeti.ContCohomology

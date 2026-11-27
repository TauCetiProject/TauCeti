/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid.Defs
public import TauCeti.GroupTheory.Coset.CoverMultiplicity
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Cuts with cover multiplicities dividing a power of `q`

Let `G` be a group with a topology in which multiplication is separately continuous (for instance
a topological group), `S` a subgroup and `A`, `J` compact open subgroups, such as levels in the
finite adelic points of a reductive group. For a finite set `T` of left cosets of `J`, the cover
multiplicity `Subgroup.coverMultiplicity S A T t` of a coset `t` counts the classes of `r ∈ S`
modulo `S ∩ A` with `r⁻¹ • t ∈ T`. This file shows that it is a genuine count: only finitely many
classes qualify, so it vanishes only when no translate of `T` by `S` contains `t`.

Given a compact set `D ⊆ G` such that for every `x ∈ D` and `u ∈ J` some power
`(x u x⁻¹) ^ q ^ n` lies in `A`, there is a finite set `T` of cosets of `J`, stable under `S ∩ A`
and made of `(S ∩ A)`-translates of cosets of points of `D`, such that the cover multiplicity is
nonzero and divides a power of `q` at every coset whose `S`-orbit meets the image of `D` (in
particular at every point of `T`). The set `T` is the union of the `(S ∩ A)`-orbits of one coset
of a point of `D` in each `S`-orbit meeting the image of `D`: it is finite because `D` meets
finitely many cosets of the open subgroup `J` and `A` is compact, and at each chosen coset `x J`
the multiplicity is the relative index `A.relIndex H`, the index of `A ∩ H` in the stabiliser
`H = S ∩ x J x⁻¹` of `x J` in `S` (`Subgroup.coverMultiplicity_eq_relIndex`), all of whose elements
have a `q`-power power in `A`.

What the cut guarantees is coverage and divisibility: every coset whose `S`-orbit meets the image
of `D` lies in a translate `r • T` with `r ∈ S`, so its multiplicity is nonzero and the inverse
weight `1 / mult(t)` is defined there, and that multiplicity divides a power of `q`, so the weight
is a unit in any ring where `q` is a unit. These are the properties of the cut that the integral
formula of ThetaLiftChainsAndTheSeesawIdentity §3.1 (c) of the roadmap uses, but they do not by
themselves express an integral as a weighted sum over `T`, and that formula is not proved here.
It is a later application with further hypotheses on the integrand `f`: besides vanishing where
the multiplicity vanishes, its orbit averages over the Bessel subgroup `R` (with `S = R_f`) must
factor as an index `[K° : J]` times an archimedean factor times `b(t_f)` whenever `t_f J ∈ T`,
for a function `b` on the cosets of `J`, and the sum over `T` is then of the values
`b(t) / mult(t)`, not of raw values of `f`.

## Main results

* `Subgroup.coverMultiplicity_ne_zero_iff`: for `A` open, `J` compact and `T` finite, the cover
  multiplicity of `t` is nonzero exactly when some translate of `T` by `S` contains `t`.
* `Subgroup.exists_finset_coverMultiplicity_dvd_pow`: the existence of the finite set `T` above.
* `Subgroup.exists_finset_coverMultiplicity_dvd_pow_of_le`: the same for levels `J ≤ A`, with `T`
  inside a subgroup `B ⊇ A` containing `D`, at the points of `T` and at the points satisfying a
  property `W` that forces their `S`-orbit to meet `D`.

## References

* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93, for the class sets of
  groups compact at infinity weighted by inverse orders of stabilisers.
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/New/UpperBound/Seesaw/IntegralAsCosetSum.lean` (declaration
  `New.Seesaw.exists_finset_coverMultiplicity_dvd_pow`); Apache 2.0, Copyright 2026 Anthropic, PBC.
  The construction of `T` from representatives of the orbits meeting a compact set follows the
  method of this proof.
-/

public section

open MulAction Pointwise

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  {S A J : Subgroup G}

/-- **The cover multiplicity is a finite count.** For `A` open, `J` compact and `T` a finite set of
left cosets of `J`, only finitely many classes of `r ∈ S` modulo `S ∩ A` satisfy `r⁻¹ • t ∈ T`, so
the cover multiplicity of `t` is nonzero exactly when one does. -/
theorem coverMultiplicity_ne_zero_iff (hA : IsOpen (A : Set G)) (hJ : IsCompact (J : Set G))
    {T : Set (G ⧸ J)} (hT : T.Finite) {t : G ⧸ J} :
    S.coverMultiplicity A T t ≠ 0 ↔ ∃ r ∈ S, r⁻¹ • t ∈ T := by
  have : DiscreteTopology (G ⧸ A) := QuotientGroup.discreteTopology hA
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective t
  -- The `r` with `r⁻¹ • xJ = yJ` form the compact set `x J y⁻¹`.
  have hsub : {r | r ∈ S ∧ r⁻¹ • (x : G ⧸ J) ∈ T} ⊆
      ⋃ τ ∈ T, (fun u ↦ x * u * τ.out⁻¹) '' (J : Set G) := by
    rintro r ⟨-, hr⟩
    refine Set.mem_biUnion hr ⟨x⁻¹ * r * (r⁻¹ • (x : G ⧸ J)).out, ?_, by group⟩
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' (r⁻¹ • (x : G ⧸ J))).symm
    simpa [mul_assoc] using this
  have hfin : (((↑) : G → G ⧸ A) '' {r | r ∈ S ∧ r⁻¹ • (x : G ⧸ J) ∈ T}).Finite :=
    ((hT.isCompact_biUnion fun τ _ ↦ hJ.image ((continuous_mul_const _).comp
      (continuous_const_mul x))).image QuotientGroup.continuous_mk).finite_of_discrete.subset
      (Set.image_mono hsub)
  rw [coverMultiplicity_def, ← Nat.pos_iff_ne_zero, Set.ncard_pos hfin, Set.image_nonempty,
    Set.Nonempty]
  simp only [Set.mem_ofPred_eq]

-- `S` is explicit: no hypothesis of the next theorem determines it.
variable (S) in
/-- **Cuts with cover multiplicities dividing a power of `q`.** Let `A` and `J` be compact open
subgroups of `G`, `S` a subgroup, `D ⊆ G` compact and `q : ℕ`, and suppose that for every `x ∈ D`
and `u ∈ J` some power `(x u x⁻¹) ^ q ^ n` lies in `A` (`n` may depend on `x` and `u`). Then there
is a finite set `T` of left cosets of `J` such that

* `T` is stable under `S ∩ A`;
* every coset in `T` is an `(S ∩ A)`-translate of the coset of a point of `D`, so the cosets in
  `T` lie in every subgroup containing `A`, `J` and `D`;
* at every coset `t` in `T`, or whose `S`-orbit meets the cosets of the points of `D`, the cover
  multiplicity of `t` is nonzero and divides a power of `q`. -/
theorem exists_finset_coverMultiplicity_dvd_pow (hA : IsCompact (A : Set G))
    (hAo : IsOpen (A : Set G)) (hJ : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G))
    {D : Set G} (hD : IsCompact D) {q : ℕ}
    (hq : ∀ x ∈ D, ∀ u ∈ J, ∃ n : ℕ, (x * u * x⁻¹) ^ q ^ n ∈ A) :
    ∃ T : Finset (G ⧸ J), (∀ a ∈ S ⊓ A, ∀ t ∈ T, a • t ∈ T) ∧
      (∀ t ∈ T, ∃ a ∈ S ⊓ A, ∃ x ∈ D, a • (x : G ⧸ J) = t) ∧
      ∀ t : G ⧸ J, (t ∈ T ∨ ∃ s ∈ S, ∃ x ∈ D, s • t = x) →
        S.coverMultiplicity A T t ≠ 0 ∧ ∃ n : ℕ, S.coverMultiplicity A T t ∣ q ^ n := by
  have : DiscreteTopology (G ⧸ J) := QuotientGroup.discreteTopology hJo
  -- One coset `ρ ∈ R` of a point of `D` in each `S`-orbit meeting the cosets of `D`.
  obtain ⟨R, hRD, hR⟩ := Set.exists_subset_bijOn (((↑) : G → G ⧸ J) '' D) (orbit S)
  -- The cut is the union of the `(S ∩ A)`-orbits of the points of `R`.
  set T : Set (G ⧸ J) := ((S ⊓ A : Subgroup G) : Set G) • R
  have hTfin : T.Finite := by
    have hR : R.Finite := (hD.image QuotientGroup.continuous_mk).finite_of_discrete.subset hRD
    refine (hR.isCompact_biUnion fun ρ _ ↦ (hA.image (continuous_mul_const ρ.out)).image
      QuotientGroup.continuous_mk).finite_of_discrete.subset ?_
    rintro _ ⟨a, ha, ρ, hρ, rfl⟩
    exact Set.mem_biUnion hρ ⟨a * ρ.out, ⟨a, ha.2, rfl⟩,
      by rw [← smul_eq_mul, MulAction.Quotient.coe_smul_out]⟩
  -- `T` meets the `S`-orbit of `ρ ∈ R` exactly in the `(S ∩ A)`-orbit of `ρ`.
  have hTorbit : ∀ ρ ∈ R, ∀ s ∈ S, s • ρ ∈ T ↔ ∃ a ∈ S ⊓ A, a • ρ = s • ρ := by
    refine fun ρ hρ s hs ↦ ⟨fun h ↦ ?_, fun ⟨a, ha, hasρ⟩ ↦ ⟨a, ha, ρ, hρ, hasρ⟩⟩
    obtain ⟨a, ha, ρ', hρ', hasρ⟩ := Set.mem_smul.1 h
    refine ⟨a, ha, ?_⟩
    have hρ'ρ : ρ' ∈ orbit S ρ :=
      ⟨⟨a⁻¹ * s, mul_mem (inv_mem ha.1) hs⟩, by simp [Subgroup.smul_def, mul_smul, ← hasρ]⟩
    obtain rfl := hR.injOn hρ' hρ (orbit_eq_iff.2 hρ'ρ)
    exact hasρ
  refine ⟨hTfin.toFinset, ?_, ?_, ?_⟩ <;>
    simp only [Set.Finite.mem_toFinset, Set.Finite.coe_toFinset]
  · rintro a ha _ ⟨b, hb, ρ, hρ, rfl⟩
    exact ⟨a * b, mul_mem ha hb, ρ, hρ, mul_smul a b ρ⟩
  · rintro _ ⟨a, ha, ρ, hρ, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hRD hρ
    exact ⟨a, ha, x, hx, rfl⟩
  intro t ht
  -- Move `t` along its `S`-orbit to the chosen coset `ρ ∈ R`.
  obtain ⟨s, hs, x, hx, hst⟩ : ∃ s ∈ S, ∃ x ∈ D, s • t = x := by
    refine ht.elim (fun ⟨a, ha, ρ, hρ, hat⟩ ↦ ?_) id
    obtain ⟨x, hx, rfl⟩ := hRD hρ
    exact ⟨a⁻¹, inv_mem ha.1, x, hx, by rw [← hat, inv_smul_smul]⟩
  obtain ⟨ρ, hρ, hρorbit⟩ := hR.surjOn ⟨(x : G ⧸ J), ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨⟨g, hg⟩, hgρ⟩ := mem_orbit_iff.1 (orbit_eq_iff.1 hρorbit)
  rw [Subgroup.mk_smul, ← hst, smul_smul] at hgρ
  rw [← coverMultiplicity_smul (mul_mem hg hs) t, hgρ]
  have hne : S.coverMultiplicity A T ρ ≠ 0 := (coverMultiplicity_ne_zero_iff hAo hJ hTfin).2
    ⟨1, one_mem S, by rw [inv_one, one_smul]; exact ⟨1, one_mem _, ρ, hρ, one_smul G ρ⟩⟩
  refine ⟨hne, exists_coverMultiplicity_dvd_pow (hTorbit ρ hρ) hne fun g hg ↦ ?_⟩
  -- An element of the stabiliser of `ρ = y J` is `y u y⁻¹` with `u ∈ J`.
  obtain ⟨y, hy, rfl⟩ := hRD hρ
  obtain ⟨n, hn⟩ := hq y hy (y⁻¹ * g * y) <| by
    simpa [mul_assoc] using inv_mem (QuotientGroup.eq.1 (mem_stabilizer_iff.1 hg.2))
  exact ⟨n, by simpa [mul_assoc] using hn⟩

/-- **Cuts for levels `J ≤ A` inside a subgroup `B`.** Let `J ≤ A` be open subgroups of `G` with
`A` compact, `B` a subgroup containing `A`, `D ⊆ B` compact, and `W` a property such that the
`S`-orbit of every point satisfying `W` meets `D`. Suppose every `x ∈ D` has an `n` with
`(x u x⁻¹) ^ q ^ n ∈ A` for all `u ∈ J`. Then there is a finite set `T` of left cosets of `J`,
stable under `S ∩ A`, whose cosets lie in `B`, such that the cover multiplicity of `x J` is
nonzero and divides a power of `q` whenever `x J ∈ T` or `W x`.

This is the form in which cuts are built in groups of finite adelic points, with `B` the points
integral at the relevant places; `Subgroup.exists_finset_coverMultiplicity_dvd_pow` is the general
statement, for compact open `A` and `J` without `B`, `W` or `J ≤ A`, and with `n` allowed to depend
on `u`. -/
theorem exists_finset_coverMultiplicity_dvd_pow_of_le (hA : IsCompact (A : Set G))
    (hJo : IsOpen (J : Set G)) (hJA : J ≤ A) {B : Subgroup G} (hAB : A ≤ B) {D : Set G}
    (hD : IsCompact D) (hDB : D ⊆ B) {q : ℕ}
    (hq : ∀ x ∈ D, ∃ n : ℕ, ∀ u ∈ J, (x * u * x⁻¹) ^ q ^ n ∈ A) {W : G → Prop}
    (hW : ∀ x, W x → ∃ s ∈ S, s * x ∈ D) :
    ∃ T : Finset (G ⧸ J), (∀ a ∈ S ⊓ A, ∀ t ∈ T, a • t ∈ T) ∧
      (∀ x : G, (x : G ⧸ J) ∈ T → x ∈ B) ∧
      ∀ x : G, ((x : G ⧸ J) ∈ T ∨ W x) →
        S.coverMultiplicity A (T : Set (G ⧸ J)) x ≠ 0 ∧
          ∃ n : ℕ, S.coverMultiplicity A (T : Set (G ⧸ J)) x ∣ q ^ n := by
  obtain ⟨T, hTA, hTD, hT⟩ := S.exists_finset_coverMultiplicity_dvd_pow hA
    (isOpen_mono hJA hJo) (hA.of_isClosed_subset (J.isClosed_of_isOpen hJo) hJA) hJo hD
    fun x hx u hu ↦ (hq x hx).imp fun n hn ↦ hn u hu
  refine ⟨T, hTA, fun x hx ↦ ?_, fun x hx ↦ hT x (hx.imp id fun hWx ↦ ?_)⟩
  · -- The coset `x J` is `a y J` with `a ∈ A` and `y ∈ D`.
    obtain ⟨a, ha, y, hy, hay⟩ := hTD _ hx
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq] at hay
    simpa [mul_assoc] using B.mul_mem (B.mul_mem (hAB ha.2) (hDB hy)) (hAB (hJA hay))
  · obtain ⟨s, hs, hsx⟩ := hW x hWx
    exact ⟨s, hs, s * x, hsx, rfl⟩

end Subgroup

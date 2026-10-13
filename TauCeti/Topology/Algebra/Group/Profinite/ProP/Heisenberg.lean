/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.MahlerBasis
public import TauCeti.Topology.Algebra.ContinuousMulEquiv
public import TauCeti.GroupTheory.GroupExtension.Of.Surjective
public import TauCeti.Topology.Algebra.Group.Heisenberg
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Extension
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Product
public import TauCeti.Topology.Separation.TypeTags

/-!
# The Heisenberg group over a pro-`p` ring is pro-`p`

Let `R` be a compact Hausdorff topological ring whose additive group is pro-`p`. Then the
Heisenberg group `HeisenbergGroup R`, with the topology of `R × R × R`, is pro-`p`
(`TauCeti.HeisenbergGroup.isProP`). It is an extension

  `1 → R → HeisenbergGroup R → R × R → 1`,

where `R` embeds as the central `z`-axis `(0, 0, z)` and the quotient map forgets the
`z`-coordinate, and pro-`p` groups are closed under extensions with compact total group
(`TauCeti.IsProP.of_ker_isProP`).

Over the `p`-adic integers this gives the compact, totally disconnected pro-`p` group
`HeisenbergGroup ℤ_[p]` of nilpotency class two (`TauCeti.HeisenbergGroup.isProP_padicInt`). By the
universal property of free pro-`p` groups it receives a continuous homomorphism from a free pro-`p`
group sending two chosen generators to `(1, 0, 0)` and `(0, 1, 0)`; since their commutator is
`(0, 0, 1)`, this detects the brackets of generators in the graded Lie ring of the closed lower
central series of a free pro-`p` group. Two facts make the detection work: the closed lower
central series of the Heisenberg group over a Hausdorff topological ring stops at `γ_2 = 1`
(`TauCeti.HeisenbergGroup.closedLowerCentralSeries_two_eq_bot`), and the `p`-adic powers of
`(0, 0, z)` are the elements `(0, 0, c z)`.

More generally, the `p`-adic powers in `HeisenbergGroup ℤ_[p]` are given by the same polynomial
formula as the natural powers, `(x, y, z) ^ c = (c x, c y, c z + (c choose 2) x y)`, with the
binomial coefficient of the binomial ring `ℤ_[p]`.

## Main results

* `TauCeti.HeisenbergGroup.isProP`: the Heisenberg group over a compact Hausdorff topological ring
  with pro-`p` additive group is pro-`p`.
* `TauCeti.HeisenbergGroup.isProP_padicInt`: the Heisenberg group over `ℤ_[p]` is pro-`p`.
* `TauCeti.HeisenbergGroup.padicPow_eq`: the `p`-adic power of `(x, y, z)` by `c` is
  `(c x, c y, c z + (c choose 2) x y)`.
* `TauCeti.HeisenbergGroup.padicPow_mk_zero_zero`: the `p`-adic power of `(0, 0, z)` by `c` is
  `(0, 0, c z)`.
* `TauCeti.HeisenbergGroup.level`, `TauCeti.HeisenbergGroup.mem_level_iff`,
  `TauCeti.HeisenbergGroup.level_zero`, `TauCeti.HeisenbergGroup.level_antitone`,
  `TauCeti.HeisenbergGroup.index_level`, `TauCeti.HeisenbergGroup.hasBasis_nhds_one_level`: the
  triples with all coordinates in `p ^ n ℤ_p` form an open normal subgroup of index `p ^ (3 n)`;
  these subgroups decrease in `n` from the whole group at `n = 0` and form a basis of
  neighbourhoods of `1`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 2.2.
-/

public section

namespace TauCeti

namespace HeisenbergGroup

open Multiplicative

variable {p : ℕ} {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R]

/-- The Heisenberg group over a compact Hausdorff topological ring whose additive group is
pro-`p` is pro-`p`. -/
theorem isProP (hR : IsProP p (Multiplicative R)) : IsProP p (HeisenbergGroup R) := by
  classical
  -- The quotient map `(x, y, z) ↦ (x, y)` onto `R × R`, whose kernel is the `z`-axis.
  let f : HeisenbergGroup R →* Multiplicative (R × R) :=
    { toFun a := ofAdd (a.x, a.y)
      map_one' := by simp
      map_mul' a b := by simp [← ofAdd_add] }
  -- The inclusion `z ↦ (0, 0, z)` of `R` onto the `z`-axis.
  let g : Multiplicative R →* HeisenbergGroup R :=
    { toFun c := ⟨0, 0, c.toAdd⟩
      map_one' := by ext <;> simp
      map_mul' a b := by ext <;> simp }
  have hf : Continuous f :=
    continuous_ofAdd.comp (continuous_x.prodMk continuous_y)
  have hg : Continuous g :=
    continuous_iff.mpr ⟨continuous_const, continuous_const, continuous_toAdd⟩
  have hker : f.ker = zAxis := by
    ext a
    simp [f, mem_zAxis_iff]
  have hgf : ∀ c, g c ∈ f.ker := by
    intro c
    simp [f, g]
  let gker := g.codRestrict f.ker hgf
  have hgker : Function.Bijective gker := by
    constructor
    · intro a b hab
      have hz := congrArg (fun c : f.ker ↦ c.val.z) hab
      simpa [gker, g] using hz
    · rintro ⟨a, ha⟩
      have hxy := mem_zAxis_iff.mp (hker ▸ ha)
      refine ⟨ofAdd a.z, ?_⟩
      apply Subtype.ext
      ext <;> simp [gker, g, hxy]
  let e : Multiplicative R ≃* f.ker := MulEquiv.ofBijective gker hgker
  have hsurj : Function.Surjective f := by
    intro c
    exact ⟨⟨c.toAdd.1, c.toAdd.2, 0⟩, by simp [f]⟩
  let S : GroupExtension (Multiplicative R) (HeisenbergGroup R)
      (Multiplicative (R × R)) :=
    GroupExtension.ofMulEquivKer hsurj e
  have hSinl : S.inl = g := by
    simp only [S, GroupExtension.ofMulEquivKer_inl]
    apply MonoidHom.ext
    intro c
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply,
      e, MulEquiv.ofBijective_apply, gker, MonoidHom.codRestrict_apply]
  have hSrh : S.rightHom = f :=
    GroupExtension.ofMulEquivKer_rightHom _ _
  have hRR : IsProP p (Multiplicative (R × R)) :=
    (hR.prod hR).of_equiv (ContinuousMulEquiv.prodMultiplicative R R).symm
  exact S.isProP (hSinl ▸ hg)
    (hSrh ▸ (MonoidHom.isOpenQuotientMap_of_isQuotientMap
      (Topology.IsQuotientMap.of_surjective_continuous hsurj hf)).isOpenMap) hR hRR

/-- The Heisenberg group over the `p`-adic integers is pro-`p`. -/
theorem isProP_padicInt (p : ℕ) [Fact p.Prime] : IsProP p (HeisenbergGroup ℤ_[p]) :=
  isProP (isProP_multiplicative_padicInt p)

/-- **The power formula for `p`-adic exponents**: in the Heisenberg group over `ℤ_[p]`,
`(x, y, z) ^ c = (c x, c y, c z + (c choose 2) x y)`, where `c choose 2` is the binomial
coefficient `Ring.choose c 2` of the binomial ring `ℤ_[p]`. -/
theorem padicPow_eq {p : ℕ} [Fact p.Prime] (a : HeisenbergGroup ℤ_[p]) (c : ℤ_[p]) :
    (isProP_padicInt p).padicPow a c =
      ⟨c * a.x, c * a.y, c * a.z + Ring.choose c 2 * (a.x * a.y)⟩ := by
  -- The right-hand side is continuous in `c` and agrees with the natural powers of `a`.
  refine ((isProP_padicInt p).eq_padicPow_of_continuous (f := fun c : ℤ_[p] ↦
    (⟨c * a.x, c * a.y, c * a.z + Ring.choose c 2 * (a.x * a.y)⟩ : HeisenbergGroup ℤ_[p]))
    (continuous_iff.mpr ⟨by fun_prop, by fun_prop, by fun_prop⟩) (fun k ↦ ?_) c).symm
  rw [pow_eq]
  simp [nsmul_eq_mul, Ring.choose_natCast]

/-- The `p`-adic power of an element `(0, 0, z)` of the `z`-axis of the Heisenberg group over
`ℤ_[p]` by `c` is `(0, 0, c z)`. -/
@[simp]
theorem padicPow_mk_zero_zero {p : ℕ} [Fact p.Prime] (z c : ℤ_[p]) :
    (isProP_padicInt p).padicPow ⟨0, 0, z⟩ c = ⟨0, 0, c * z⟩ := by
  simp [padicPow_eq]

section Level

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- Reduction of the coordinates modulo `p ^ n`, `HeisenbergGroup ℤ_[p] →* HeisenbergGroup
(ZMod (p ^ n))`, is continuous for the discrete topology on the target. -/
theorem continuous_map_toZModPow : Continuous (map (PadicInt.toZModPow (p := p) n)) :=
  continuous_map _ (PadicInt.continuous_toZModPow n)

/-- **The level `p ^ n` of the Heisenberg group over `ℤ_p`**: the open normal subgroup of triples
whose three coordinates lie in `p ^ n ℤ_p` (`mem_level_iff`), the kernel of reduction modulo
`p ^ n`. It has index `p ^ (3 n)` (`index_level`), and the levels form a basis of neighbourhoods
of `1` (`hasBasis_nhds_one_level`). -/
noncomputable def level : OpenNormalSubgroup (HeisenbergGroup ℤ_[p]) :=
  (openNormalSubgroupBot (HeisenbergGroup (ZMod (p ^ n)))).comap
    (map (PadicInt.toZModPow (p := p) n)) (continuous_map_toZModPow p n)

/-- The underlying subgroup of the level `p ^ n` is the kernel of reduction modulo `p ^ n`. -/
@[simp]
theorem level_toSubgroup :
    (level p n).toSubgroup = (map (PadicInt.toZModPow (p := p) n)).ker := by
  rw [level, OpenNormalSubgroup.toSubgroup_comap, openNormalSubgroupBot_toSubgroup,
    MonoidHom.comap_bot]

/-- The level `p ^ n` consists of the triples whose coordinates are all multiples of `p ^ n`. -/
@[simp]
theorem mem_level_iff {a : HeisenbergGroup ℤ_[p]} :
    a ∈ level p n ↔
      (p : ℤ_[p]) ^ n ∣ a.x ∧ (p : ℤ_[p]) ^ n ∣ a.y ∧ (p : ℤ_[p]) ^ n ∣ a.z := by
  simp only [level, OpenNormalSubgroup.mem_comap, mem_openNormalSubgroupBot, map_apply,
    ← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  constructor
  · intro h
    exact ⟨congrArg x h, congrArg y h, congrArg z h⟩
  · rintro ⟨hx, hy, hz⟩
    ext <;> simp [hx, hy, hz]

/-- The level `p ^ 0` is the whole group. -/
@[simp]
theorem level_zero : level p 0 = openNormalSubgroupTop (HeisenbergGroup ℤ_[p]) :=
  OpenNormalSubgroup.toSubgroup_injective <| by
    simp only [openNormalSubgroupTop_toSubgroup, Subgroup.eq_top_iff']
    exact fun a ↦ (mem_level_iff p 0).mpr (by simp)

/-- The levels decrease as the exponent grows. -/
theorem level_antitone : Antitone (level p) := fun m n hmn a ha ↦ by
  obtain ⟨hx, hy, hz⟩ := (mem_level_iff p n).mp ha
  have h := pow_dvd_pow (p : ℤ_[p]) hmn
  exact (mem_level_iff p m).mpr ⟨h.trans hx, h.trans hy, h.trans hz⟩

/-- The kernel of reduction modulo `p ^ n` on the Heisenberg group over `ℤ_[p]` has index
`p ^ (3 n)`. -/
@[simp]
theorem index_ker_map_toZModPow :
    (map (PadicInt.toZModPow (p := p) n)).ker.index = p ^ (3 * n) := by
  rw [← MonoidHom.comap_bot, Subgroup.index_comap_of_surjective ⊥
      (map_surjective (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) n))),
    Subgroup.index_bot, card_eq, Nat.card_zmod, ← pow_mul, mul_comm]

/-- **The level `p ^ n` has index `p ^ (3 n)`.** -/
theorem index_level : (level p n).toSubgroup.index = p ^ (3 * n) := by
  rw [level_toSubgroup, index_ker_map_toZModPow]

/-- **The levels form a basis of neighbourhoods of `1`.** -/
theorem hasBasis_nhds_one_level :
    (nhds (1 : HeisenbergGroup ℤ_[p])).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (level p n : Set (HeisenbergGroup ℤ_[p]))) := by
  refine ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨m, _, hm⟩ ↦
    Filter.mem_of_superset ((level p m).isOpen.mem_nhds (level p m).one_mem) hm⟩⟩
  have h1 : homeomorphProd.symm ((0, 0, 0) : ℤ_[p] × ℤ_[p] × ℤ_[p]) = 1 := by
    ext <;> simp
  have hU' : homeomorphProd.symm ⁻¹' U ∈ nhds ((0, 0, 0) : ℤ_[p] × ℤ_[p] × ℤ_[p]) :=
    homeomorphProd.symm.continuous.continuousAt.preimage_mem_nhds (h1 ▸ hU)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU'
  obtain ⟨m, hm⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨m, trivial, fun a ha ↦ ?_⟩
  have hnorm (c : ℤ_[p]) (hc : (p : ℤ_[p]) ^ m ∣ c) : ‖c‖ < ε :=
    ((PadicInt.norm_le_pow_iff_mem_span_pow c m).mpr (Ideal.mem_span_singleton.mpr hc)).trans_lt
      hm
  obtain ⟨hx, hy, hz⟩ := (mem_level_iff p m).mp ha
  have hmem : (a.x, a.y, a.z) ∈ Metric.ball ((0, 0, 0) : ℤ_[p] × ℤ_[p] × ℤ_[p]) ε := by
    simp only [Metric.mem_ball, Prod.dist_eq, dist_zero_right, max_lt_iff]
    exact ⟨hnorm _ hx, hnorm _ hy, hnorm _ hz⟩
  simpa using hεU hmem

end Level

end HeisenbergGroup

end TauCeti

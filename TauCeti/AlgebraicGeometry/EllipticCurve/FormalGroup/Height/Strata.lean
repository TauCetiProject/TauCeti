/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Ideal
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Supersingular
import Mathlib.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Ideal.Quotient.Coprime
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Higher height ideals and Landweber regularity for Weierstrass formal groups

Let `W` be a Weierstrass curve over a commutative ring `R`, `Ê` its formal group law, and `p` a
prime. Over any residue field of characteristic `p`, `Ê` has height `⊤` on the cuspidal locus
`c₄ = Δ = 0` and height `1` or `2` on the smooth-or-nodal locus (`c₄ ≠ 0` or `Δ ≠ 0`)
(`WeierstrassCurve.height_formalGroup_eq_top_iff`,
`WeierstrassCurve.height_formalGroup_le_two_iff`). Reading the universal property of the height
ideals (`FormalGroup.heightIdeal_le_ker_iff`) into the residue fields `FractionRing (R ⧸ P)` of
prime ideals `P` of `R` shows that for every `n ≥ 3`:

* a prime ideal `P` contains `I_n(Ê)` if and only if it contains `(p, c₄, Δ)`
  (`WeierstrassCurve.heightIdeal_formalGroup_le_prime_iff`);
* the radical of `I_n(Ê)` is the radical of `(p, c₄, Δ)`
  (`WeierstrassCurve.radical_heightIdeal_formalGroup`);
* `I_n(Ê) = R` if and only if `(p, c₄, Δ) = R`
  (`WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff`).

By Landweber's recursion `I₃(Ê) = I₂(Ê) + (v₂)`, where `v₂` is the coefficient of `T ^ (p ^ 2)` in
`[p]_Ê`, the condition `I₃(Ê) = R` is equivalent to `v₂` being a unit in `R ⧸ I₂(Ê) = R ⧸ (p, A)`
(`WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_iff`). In particular, whenever `W` has
no cusps in characteristic `p` (`(p, c₄, Δ) = R`, which holds whenever `(c₄, Δ) = R` and in
particular for every elliptic curve `[W.IsElliptic]`), `v₂` is a unit modulo `I₂(Ê)` and `I_n(Ê)` is
the unit ideal for all `n ≥ 3`.

Consequently, on any smooth-or-nodal Weierstrass curve at `p`, multiplication by `v₂` on
`M ⧸ I₂(Ê) M` is an isomorphism and `M ⧸ I₃(Ê) M = 0`, so every Landweber sequence
`(p, v₁, v₂, …, v_{n-1})` of length `n ≥ 2` is weakly regular on an `R`-module `M` if and only if
`(p, A)` is weakly regular on `M`
(`WeierstrassCurve.isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_iff`).

## Main results

* `WeierstrassCurve.heightIdeal_formalGroup_le_prime_iff`: for `n ≥ 3`, a prime ideal contains
  `I_n(Ê)` if and only if it contains `(p, c₄, Δ)`.
* `WeierstrassCurve.radical_heightIdeal_formalGroup`: for `n ≥ 3`, `√I_n(Ê) = √(p, c₄, Δ)`.
* `WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff`: for `n ≥ 3`, `I_n(Ê) = ⊤` if and only if
  `Ideal.span {(p : R), W.c₄, W.Δ} = ⊤`, with specializations to `Ideal.span {W.c₄, W.Δ} = ⊤` and
  `[W.IsElliptic]`.
* `WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_iff`: Landweber's `v₂` is a unit in
  `R ⧸ I₂(Ê)` if and only if `Ideal.span {(p : R), W.c₄, W.Δ} = ⊤`, with specializations to
  `Ideal.span {W.c₄, W.Δ} = ⊤` and `[W.IsElliptic]`.
* `WeierstrassCurve.isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_iff`: when
  `Ideal.span {(p : R), W.c₄, W.Δ} = ⊤` and `n ≥ 2`, weak regularity of `(v₀, …, v_{n-1})` on `M`
  is equivalent to weak regularity of `(p, A)` on `M`.

## References

* P. S. Landweber, *Homological properties of comodules over `MU_*(MU)` and `BP_*(BP)`*,
  Amer. J. Math. 98 (1976), 591–610.
* P. G. Goerss, *Topological modular forms [after Hopkins, Miller and Lurie]*, Séminaire Bourbaki
  1005 (2009), §3.2.
* J. Lurie, *A Survey of Elliptic Cohomology*, §2.3.
-/

public section

open RingTheory.Sequence

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {p : ℕ}

/-- **Prime ideals containing `I_n(Ê)` for `n ≥ 3`.** For a prime `p` and `n ≥ 3`, a prime ideal
`P` of `R` contains `(formalGroup W).heightIdeal p n` if and only if `P` contains `p`, `W.c₄`, and
`W.Δ`. -/
theorem heightIdeal_formalGroup_le_prime_iff (hp : p.Prime) {n : ℕ} (hn : 3 ≤ n) {P : Ideal R}
    [P.IsPrime] :
    (formalGroup W).heightIdeal p n ≤ P ↔ Ideal.span {(p : R), W.c₄, W.Δ} ≤ P := by
  have : Fact p.Prime := ⟨hp⟩
  let K := FractionRing (R ⧸ P)
  let φ : R →+* K := (algebraMap (R ⧸ P) K).comp (Ideal.Quotient.mk P)
  have hker : RingHom.ker φ = P := by
    ext x
    simp [φ, RingHom.mem_ker,
      map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ P) K), Ideal.Quotient.eq_zero_iff_mem]
  have hmem {x : R} : φ x = 0 ↔ x ∈ P := by rw [← RingHom.mem_ker, hker]
  have hchar (hpP : (p : R) ∈ P) : CharP K p :=
    (CharP.charP_iff_prime_eq_zero hp).mpr (by rw [← map_natCast φ]; exact hmem.mpr hpP)
  simp only [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  constructor
  · intro hle
    have hpP : (p : R) ∈ P := hle <| (formalGroup W).heightIdeal_mono (by omega : 1 ≤ n) <| by
      rw [(formalGroup W).heightIdeal_one hp]; exact Ideal.mem_span_singleton_self _
    have := hchar hpP
    have hord : ((p ^ n : ℕ) : ℕ∞) ≤ ((formalGroup (W.map φ)).nsmulSeries p).order := by
      rwa [map_formalGroup, ← FormalGroup.heightIdeal_le_ker_iff, hker]
    have hnh : (n : ℕ∞) ≤ (formalGroup (W.map φ)).height p :=
      ((formalGroup (W.map φ)).heightIdeal_eq_bot_iff_le_height (p := p)).mp
        ((formalGroup (W.map φ)).heightIdeal_eq_bot_iff.mpr hord)
    have hnotle : ¬(formalGroup (W.map φ)).height p ≤ 2 := fun h2 ↦
      absurd (le_trans (by exact_mod_cast hn) (hnh.trans h2) : (3 : ℕ∞) ≤ 2) (by decide)
    have hcΔ : (W.map φ).c₄ = 0 ∧ (W.map φ).Δ = 0 := by
      simpa only [not_or, not_ne_iff] using mt (W.map φ).height_formalGroup_le_two_iff.mpr hnotle
    exact ⟨hpP, hmem.mp (by simpa using hcΔ.1), hmem.mp (by simpa using hcΔ.2)⟩
  · rintro ⟨hpP, hc₄P, hΔP⟩
    have := hchar hpP
    have htop : (formalGroup (W.map φ)).height p = ⊤ :=
      (W.map φ).height_formalGroup_eq_top_of_c₄_eq_zero
        (by simpa using hmem.mpr hΔP) (by simpa using hmem.mpr hc₄P)
    rw [← hker, FormalGroup.heightIdeal_le_ker_iff, ← map_formalGroup,
      ((formalGroup (W.map φ)).height_eq_top_iff).mp htop, PowerSeries.order_zero]
    exact le_top

/-- **The radical of `I_n(Ê)` for `n ≥ 3` is `√(p, c₄, Δ)`.** -/
theorem radical_heightIdeal_formalGroup (hp : p.Prime) {n : ℕ} (hn : 3 ≤ n) :
    ((formalGroup W).heightIdeal p n).radical = (Ideal.span {(p : R), W.c₄, W.Δ}).radical := by
  rw [Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
  congr 1
  ext P
  exact and_congr_left fun hP ↦ W.heightIdeal_formalGroup_le_prime_iff hp hn (P := P)

/-- **For `n ≥ 3`, `I_n(Ê) = ⊤` if and only if `(p, c₄, Δ) = ⊤`.** -/
theorem heightIdeal_formalGroup_eq_top_iff (hp : p.Prime) {n : ℕ} (hn : 3 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ ↔ Ideal.span {(p : R), W.c₄, W.Δ} = ⊤ := by
  rw [← Ideal.radical_eq_top, W.radical_heightIdeal_formalGroup hp hn, Ideal.radical_eq_top]

/-- **On the smooth-or-nodal locus `(c₄, Δ) = ⊤`, `I_n(Ê) = ⊤` for all `n ≥ 3`.** -/
theorem heightIdeal_formalGroup_eq_top_of_span_c₄_Δ_eq_top (hp : p.Prime)
    (hW : Ideal.span {W.c₄, W.Δ} = ⊤) {n : ℕ} (hn : 3 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ := by
  rw [W.heightIdeal_formalGroup_eq_top_iff hp hn, Ideal.span_insert, hW, sup_top_eq]

/-- **For an elliptic curve over any commutative ring, `I_n(Ê) = ⊤` for all `n ≥ 3`.** -/
theorem heightIdeal_formalGroup_eq_top [W.IsElliptic] (hp : p.Prime) {n : ℕ} (hn : 3 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ := by
  refine W.heightIdeal_formalGroup_eq_top_of_span_c₄_Δ_eq_top hp ?_ hn
  rw [Ideal.span_insert, Ideal.span_singleton_eq_top.mpr W.isUnit_Δ, sup_top_eq]

/-- **Invertibility of Landweber's `v₂` modulo `I₂(Ê)`.** For a prime `p`, the coefficient `v₂` of
`T ^ (p ^ 2)` in `[p]_Ê(T)` is a unit in `R ⧸ I₂(Ê)` if and only if `(p, c₄, Δ) = ⊤`. -/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup_iff (hp : p.Prime) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
        (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) ↔
      Ideal.span {(p : R), W.c₄, W.Δ} = ⊤ := by
  rw [Ideal.Quotient.isUnit_mk_iff, sup_comm, ← (formalGroup W).heightIdeal_succ hp 2,
    W.heightIdeal_formalGroup_eq_top_iff hp le_rfl]

/-- **On the smooth-or-nodal locus `(c₄, Δ) = ⊤`, Landweber's `v₂` is a unit modulo `I₂(Ê)`.** -/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup_of_span_c₄_Δ_eq_top (hp : p.Prime)
    (hW : Ideal.span {W.c₄, W.Δ} = ⊤) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) := by
  rw [W.isUnit_mk_coeff_nsmulSeries_formalGroup_iff hp, Ideal.span_insert, hW, sup_top_eq]

/-- **On an elliptic curve over any commutative ring, Landweber's `v₂` is a unit modulo
`I₂(Ê)`.** -/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup [W.IsElliptic] (hp : p.Prime) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) := by
  refine W.isUnit_mk_coeff_nsmulSeries_formalGroup_of_span_c₄_Δ_eq_top hp ?_
  rw [Ideal.span_insert, Ideal.span_singleton_eq_top.mpr W.isUnit_Δ, sup_top_eq]

/-- **Landweber regularity reduces to `(p, A)` away from cusps.** When
`Ideal.span {(p : R), W.c₄, W.Δ} = ⊤`, a Landweber sequence `(v₀, v₁, …, v_{n-1})` of length
`n ≥ 2` for `formalGroup W` at a prime `p` is weakly regular on an `R`-module `M` if and only if
`(p, A)` is weakly regular on `M`, where `A` is the Hasse invariant. -/
theorem isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_iff (hp : p.Prime)
    (hW : Ideal.span {(p : R), W.c₄, W.Δ} = ⊤) {n : ℕ} (hn : 2 ≤ n) (M : Type*)
    [AddCommGroup M] [Module R M] :
    IsWeaklyRegular M
        (List.ofFn fun i : Fin n ↦
          PowerSeries.coeff (p ^ (i : ℕ)) ((formalGroup W).nsmulSeries p)) ↔
      IsWeaklyRegular M
        [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] := by
  set v : ℕ → R := fun i ↦ PowerSeries.coeff (p ^ i) ((formalGroup W).nsmulSeries p)
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
  have hhead : (List.ofFn fun i : Fin 2 ↦ v i) = [(p : R), v 1] := by
    simp [List.ofFn_succ, v, pow_one]
  change IsWeaklyRegular M (List.ofFn fun i : Fin (2 + k) ↦ v i) ↔ _
  rw [List.ofFn_add]
  simp only [Fin.val_castLE, hhead, isWeaklyRegular_append_iff']
  refine (and_iff_left ?_).trans ?_
  swap
  · simpa [v] using W.isWeaklyRegular_natCast_coeff_nsmulSeries_iff hp M
  rcases k with _ | k
  · simp [IsWeaklyRegular.nil]
  · set I := Ideal.ofList [(p : R), v 1]
    have hI : I = (formalGroup W).heightIdeal p 2 := by
      change Ideal.ofList [(p : R), v 1] = _
      rw [← hhead, Ideal.ofList_ofFn, (formalGroup W).heightIdeal_eq_span hp 2]
      congr 1
      ext x
      simp [Fin.exists_iff, v]
    obtain ⟨u, hu⟩ : IsUnit (Ideal.Quotient.mk I (v 2)) :=
      hI.symm ▸ (W.isUnit_mk_coeff_nsmulSeries_formalGroup_iff hp).mpr hW
    simp only [List.ofFn_succ, Fin.val_natAdd, Fin.val_zero, add_zero, List.map_cons,
      isWeaklyRegular_cons_iff]
    rw [← hu]
    have : Subsingleton (QuotSMulTop (u : R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) := by
      rw [QuotSMulTop, Submodule.Quotient.subsingleton_iff, eq_top_iff]
      exact fun x _ ↦ Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mpr
        ⟨(↑u⁻¹ : R ⧸ I) • x, trivial, by rw [← mul_smul, u.mul_inv, one_smul]⟩
    exact ⟨u.isSMulRegular _, IsWeaklyRegular.of_subsingleton _⟩

/-- **Landweber regularity for an elliptic curve reduces to `(p, A)`.** For an elliptic curve `W`
over `R`, a prime `p`, and `n ≥ 2`, the Landweber sequence `(v₀, v₁, …, v_{n-1})` is weakly regular
on `M` if and only if `(p, A)` is weakly regular on `M`. -/
theorem isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_iff_of_isElliptic [W.IsElliptic]
    (hp : p.Prime) {n : ℕ} (hn : 2 ≤ n) (M : Type*) [AddCommGroup M] [Module R M] :
    IsWeaklyRegular M
        (List.ofFn fun i : Fin n ↦
          PowerSeries.coeff (p ^ (i : ℕ)) ((formalGroup W).nsmulSeries p)) ↔
      IsWeaklyRegular M
        [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] := by
  refine W.isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_iff hp ?_ hn M
  rw [Ideal.span_insert, Ideal.span_insert, Ideal.span_singleton_eq_top.mpr W.isUnit_Δ,
    sup_top_eq, sup_top_eq]

end WeierstrassCurve

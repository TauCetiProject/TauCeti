/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Pair
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Basic

/-!
# The integral tilt of a complete uniform Tate ring

Let `B` be a complete Hausdorff uniform Tate ring in which `p` is topologically nilpotent, with
tilt `B♭ = uniformTilt p B`, and let `B⁺ ⊆ B°` be a ring of integral elements. The *integral tilt*
`B♭⁺ = lim_{x ↦ x ^ p} B⁺` is the set of elements of `B♭` all of whose coordinates lie in `B⁺`; it
is a subring of `B♭`, and it is the set of `x` with `x⁽⁰⁾ ∈ B⁺`.

The coordinates are additive modulo `p` on `B♭⁺`: `(x + y)⁽ⁱ⁾ - x⁽ⁱ⁾ - y⁽ⁱ⁾ ∈ p • B⁺`
(`TauCeti.Perfectoid.uniformTilt.coeff_add_sub_mem_of_forall_mem`). Consequently, for an ideal
`I` of `B⁺` such that `B⁺` is `I`-adically complete and `B⁺ ⧸ I` has characteristic `p` (for
instance an ideal of definition containing `p`), reducing every coordinate modulo `I` is a ring
isomorphism `B♭⁺ ≃+* lim_{x ↦ x ^ p} B⁺ ⧸ I` onto the perfection of `B⁺ ⧸ I`. If the topology
of `B⁺` is `I`-adic, this is a homeomorphism for the inverse-limit topology with discrete
quotient factors (`isHomeomorph_plusEquiv`). Its multiplicative
part is Mathlib's `Perfection.quotientMulEquiv`, whose inverse is built from the Teichmüller map;
the ring structure on the target is the coordinatewise one of Mathlib's `Perfection`. So the ring
structure of the tilt, defined through limits, is identified on `B♭⁺` with an algebraically defined
one; for `I = (p)` the target is Mathlib's `PreTilt B⁺ p = Perfection (ModP B⁺ p) p`.

## Main definitions

* `TauCeti.Perfectoid.uniformTilt.plusSubring h`: the integral tilt `B♭⁺ = lim_{x ↦ x ^ p} B⁺` of a
  ring of integral elements `B⁺` (given by `h : IsRingOfIntegralElements B⁺`), as a subring of the
  tilt.
* `TauCeti.Perfectoid.uniformTilt.plusSharp p h`: the sharp map `B♭⁺ →*₀ B⁺`, `x ↦ x♯ = x⁽⁰⁾`.
* `TauCeti.Perfectoid.uniformTilt.plusEquiv h I`: the ring isomorphism
  `B♭⁺ ≃+* Perfection (B⁺ ⧸ I) p`, `x ↦ (x⁽ⁿ⁾ mod I)ₙ`.

## Main results

* `TauCeti.Perfectoid.uniformTilt.mem_plusSubring_iff_coeff_zero`: `x ∈ B♭⁺` iff `x⁽⁰⁾ ∈ B⁺`.
* `TauCeti.Perfectoid.uniformTilt.coeff_add_sub_mem_span`: `(x + y)⁽ⁿ⁾ - x⁽ⁿ⁾ - y⁽ⁿ⁾ ∈ p B⁺` on
  `B♭⁺`.
* `TauCeti.Perfectoid.uniformTilt.plusSharp_add_sub_mem`: `(x + y)♯ - x♯ - y♯ ∈ p B⁺`.
* `TauCeti.Perfectoid.uniformTilt.coeff_plusEquiv`: `plusEquiv` reduces every coordinate modulo `I`.
* `TauCeti.Perfectoid.uniformTilt.coeff_zero_plusEquiv_symm`: the zeroth coordinate of the inverse
  is the Teichmüller map `Perfection (B⁺ ⧸ I) p → B⁺`.
* `TauCeti.Perfectoid.uniformTilt.isHomeomorph_plusEquiv`: the topological inverse-limit comparison.

## References

* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, in
  *Perfectoid Spaces: Lectures from the 2017 Arizona Winter School*, Lemma 2.7.1(b).
* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.10 and its proof.
* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Lemma 3.2(i).
-/

public section

open Filter Pointwise TauCeti.Huber

namespace TauCeti.Perfectoid.uniformTilt

variable {p : ℕ} {B : Type*} [CommRing B] [hp : Fact p.Prime] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [hpn : Fact (IsTopologicallyNilpotent (p : B))]

variable {Bplus : Subring B}

variable (p) in
/-- The *integral tilt* `B♭⁺ = lim_{x ↦ x ^ p} B⁺` of a ring of integral elements `B⁺ ⊆ B°`: the
subring of the tilt of elements all of whose coordinates lie in `B⁺`. -/
noncomputable def plusSubring (h : IsRingOfIntegralElements Bplus) :
    Subring (uniformTilt p B) where
  carrier := {x | ∀ n, coeff p B n x ∈ Bplus}
  mul_mem' hx hy n := by
    rw [map_mul]
    exact mul_mem (hx n) (hy n)
  one_mem' n := by
    rw [map_one]
    exact one_mem _
  add_mem' {x y} hx hy n := by
    obtain ⟨z, hz, he⟩ := Set.mem_smul_set.mp <| coeff_add_sub_mem_of_forall_mem
      (Bplus.toAddSubgroup.isClosed_of_isOpen h.isOpen) h.le_powerBoundedSubring hx hy n
    rw [smul_eq_mul] at he
    have hsum : coeff p B n (x + y) = p * z + coeff p B n x + coeff p B n y := by
      linear_combination -he
    rw [hsum]
    exact add_mem (add_mem (mul_mem (natCast_mem _ p) hz) (hx n)) (hy n)
  zero_mem' n := by
    rw [coeff_zero]
    exact zero_mem _
  neg_mem' {x} hx n := by
    -- `-x = (-1) * x`, and the coordinates of `-1` square to `1`, so are integral over `B⁺`
    have h1 : coeff p B n (-1 : uniformTilt p B) ∈ Bplus :=
      h.mem_of_pow_mem two_pos (by rw [← map_pow, neg_one_sq, map_one]; exact one_mem _)
    rw [← neg_one_mul, map_mul]
    exact mul_mem h1 (hx n)

/-- An element lies in the integral tilt iff all of its coordinates lie in `B⁺`. -/
theorem mem_plusSubring_iff {h : IsRingOfIntegralElements Bplus} {x : uniformTilt p B} :
    x ∈ plusSubring p h ↔ ∀ n, coeff p B n x ∈ Bplus := Iff.rfl

/-- An element lies in the integral tilt iff its zeroth coordinate `x⁽⁰⁾` lies in `B⁺`. -/
@[simp]
theorem mem_plusSubring_iff_coeff_zero {h : IsRingOfIntegralElements Bplus}
    {x : uniformTilt p B} : x ∈ plusSubring p h ↔ coeff p B 0 x ∈ Bplus := by
  refine ⟨fun hx ↦ hx 0, fun hx n ↦ h.mem_of_pow_mem (pow_pos hp.out.pos n) ?_⟩
  have hn := coeff_pow_p_pow x 0 n
  rw [zero_add] at hn
  rwa [hn]

/-- Inclusion of rings of integral elements induces inclusion of their integral tilts. -/
theorem plusSubring_mono {Cplus : Subring B} (hB : IsRingOfIntegralElements Bplus)
    (hC : IsRingOfIntegralElements Cplus) (hBC : Bplus ≤ Cplus) :
    plusSubring p hB ≤ plusSubring p hC :=
  fun _ hx ↦ mem_plusSubring_iff_coeff_zero.mpr
    (hBC (mem_plusSubring_iff_coeff_zero.mp hx))

/-- The integral tilt is an open subring: membership is tested on the zeroth coordinate. -/
theorem isOpen_plusSubring {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus) :
    IsOpen (plusSubring p h : Set (uniformTilt p B)) := by
  have he : (plusSubring p h : Set (uniformTilt p B)) = coeff p B 0 ⁻¹' Bplus :=
    Set.ext fun _ ↦ mem_plusSubring_iff_coeff_zero
  rw [he]
  exact h.isOpen.preimage (continuous_coeff 0)

/-- The integral tilt is bounded, because each coordinate lies in the bounded ring `B°`. -/
theorem isBounded_plusSubring {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus) :
    IsBounded (plusSubring p h : Set (uniformTilt p B)) := by
  rw [Huber.isBounded_iff]
  intro U hU
  rw [isEmbedding_coeff.isInducing.nhds_eq_comap] at hU
  obtain ⟨W, hW, hWU⟩ := Filter.mem_comap.mp hU
  simp only [coeff_zero, nhds_pi] at hW
  obtain ⟨s, hs, V, hV, hVW⟩ := Filter.mem_pi.mp hW
  choose T hT hTV using fun n ↦
    Huber.isBounded_iff.mp IsUniform.isBounded_powerBoundedSubring (V n) (hV n)
  refine ⟨⋂ n ∈ s, coeff p B n ⁻¹' T n, ?_, ?_⟩
  · exact (Filter.biInter_mem hs).mpr fun n _ ↦
      (continuous_coeff n).continuousAt.preimage_mem_nhds (by simpa using hT n)
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    apply hWU
    apply hVW
    intro n hn
    dsimp only
    rw [map_mul]
    exact hTV n (Set.mul_mem_mul (Set.mem_iInter₂.mp hx n hn)
      (h.le_powerBoundedSubring (mem_plusSubring_iff.mp hy n)))

/-- The integral tilt is contained in the power-bounded subring of the tilt. -/
theorem plusSubring_le_powerBoundedSubring [NonarchimedeanAddGroup (uniformTilt p B)]
    (h : IsRingOfIntegralElements Bplus) :
    plusSubring p h ≤ powerBoundedSubring (uniformTilt p B) :=
  fun _ hx ↦ mem_powerBoundedSubring.mpr ((isBounded_plusSubring h).isPowerBounded_of_mem hx)

variable (p) in
/-- The *sharp map* `x ↦ x♯ = x⁽⁰⁾` of the integral tilt, as a multiplicative map `B♭⁺ → B⁺`. It
is not additive, only additive modulo `p` (`plusSharp_add_sub_mem`). -/
noncomputable def plusSharp (h : IsRingOfIntegralElements Bplus) :
    plusSubring p h →*₀ Bplus where
  toFun x := ⟨coeff p B 0 x, mem_plusSubring_iff.mp x.2 0⟩
  map_zero' := Subtype.ext (coeff_zero 0)
  map_one' := Subtype.ext <| by simp
  map_mul' x y := Subtype.ext (map_mul (coeff p B 0) (x : uniformTilt p B) y)

@[simp]
theorem coe_plusSharp (h : IsRingOfIntegralElements Bplus) (x : plusSubring p h) :
    (plusSharp p h x : B) = coeff p B 0 x :=
  (rfl)

/-- The coordinates of the integral tilt are additive modulo `p`:
`(x + y)⁽ⁿ⁾ - x⁽ⁿ⁾ - y⁽ⁿ⁾ ∈ p B⁺` for `x, y ∈ B♭⁺`. -/
theorem coeff_add_sub_mem_span (h : IsRingOfIntegralElements Bplus) (x y : plusSubring p h)
    (n : ℕ) :
    (⟨coeff p B n (x + y), mem_plusSubring_iff.mp (x + y).2 n⟩ -
        ⟨coeff p B n x, mem_plusSubring_iff.mp x.2 n⟩ -
        ⟨coeff p B n y, mem_plusSubring_iff.mp y.2 n⟩ : Bplus) ∈
      Ideal.span {(p : Bplus)} := by
  obtain ⟨z, hz, he⟩ := Set.mem_smul_set.mp <| coeff_add_sub_mem_of_forall_mem
    (Bplus.toAddSubgroup.isClosed_of_isOpen h.isOpen) h.le_powerBoundedSubring
    (mem_plusSubring_iff.mp x.2) (mem_plusSubring_iff.mp y.2) n
  refine Ideal.mem_span_singleton'.mpr ⟨⟨z, hz⟩, Subtype.ext ?_⟩
  rw [smul_eq_mul, ← Subring.coe_add] at he
  simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, Subring.coe_natCast]
  linear_combination he

/-- **The sharp map is additive modulo `p`**: `(x + y)♯ - x♯ - y♯ ∈ p B⁺` for `x, y ∈ B♭⁺`. -/
theorem plusSharp_add_sub_mem (h : IsRingOfIntegralElements Bplus) (x y : plusSubring p h) :
    plusSharp p h (x + y) - plusSharp p h x - plusSharp p h y ∈
      Ideal.span {(p : Bplus)} :=
  coeff_add_sub_mem_span h x y 0

/-- The integral tilt is multiplicatively the perfection of the monoid `B⁺`. -/
private noncomputable def plusMulEquiv (h : IsRingOfIntegralElements Bplus) :
    plusSubring p h ≃* Perfection Bplus p where
  toFun x := ⟨fun n ↦ ⟨coeff p B n x, mem_plusSubring_iff.mp x.2 n⟩,
    fun n ↦ Subtype.ext (coeff_pow_p _ n)⟩
  invFun y := ⟨mk (fun n ↦ (y.1 n : B)) fun n ↦ congrArg Subtype.val (y.2 n),
    mem_plusSubring_iff.mpr fun n ↦ by rw [coeff_mk]; exact (y.1 n).2⟩
  left_inv x := Subtype.ext <| ext fun n ↦ by rw [coeff_mk]
  right_inv y := Perfection.extMonoid fun n ↦ Subtype.ext (coeff_mk _ _ n)
  map_mul' x y :=
    Perfection.extMonoid fun n ↦ Subtype.ext (map_mul (coeff p B n) (x : uniformTilt p B) y)

private theorem coeffMonoidHom_plusMulEquiv (h : IsRingOfIntegralElements Bplus)
    (x : plusSubring p h) (n : ℕ) :
    Perfection.coeffMonoidHom Bplus p n (plusMulEquiv h x) =
      ⟨coeff p B n x, mem_plusSubring_iff.mp x.2 n⟩ := rfl

private theorem coeff_plusMulEquiv_symm (h : IsRingOfIntegralElements Bplus)
    (y : Perfection Bplus p) (n : ℕ) :
    coeff p B n ((plusMulEquiv h).symm y : uniformTilt p B) =
      Perfection.coeffMonoidHom Bplus p n y :=
  coeff_mk _ _ n

variable (h : IsRingOfIntegralElements Bplus) (I : Ideal Bplus) [CharP (Bplus ⧸ I) p]
  [IsAdicComplete I Bplus]

/-- **The integral tilt is the perfection of `B⁺ ⧸ I`**: for an ideal `I` of `B⁺` such that `B⁺` is
`I`-adically complete and `B⁺ ⧸ I` has characteristic `p`, reducing every coordinate modulo `I` is
a ring isomorphism `B♭⁺ ≃+* Perfection (B⁺ ⧸ I) p`. -/
noncomputable def plusEquiv : plusSubring p h ≃+* Perfection (Bplus ⧸ I) p :=
  { (plusMulEquiv h).trans (Perfection.quotientMulEquiv p I) with
    map_add' x y := by
      refine Perfection.ext fun n ↦ ?_
      simp only [MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
        MulEquiv.trans_apply, Perfection.coeff_quotientMulEquiv, map_add]
      rw [← map_add, Ideal.Quotient.eq, ← sub_sub]
      -- the coordinates of `x + y` and of `x`, `y` differ by an element of `p • B⁺ ⊆ I`
      exact (Ideal.span_singleton_le_iff_mem I).mpr (I.natCast_mem_of_charP_quotient p)
        (coeff_add_sub_mem_span h x y n) }

private theorem plusEquiv_symm_apply (y : Perfection (Bplus ⧸ I) p) :
    (plusEquiv h I).symm y = (plusMulEquiv h).symm ((Perfection.quotientMulEquiv p I).symm y) :=
  rfl

/-- `plusEquiv` reduces every coordinate modulo `I`. -/
@[simp]
theorem coeff_plusEquiv (x : plusSubring p h) (n : ℕ) :
    Perfection.coeff (Bplus ⧸ I) p n (plusEquiv h I x) =
      Ideal.Quotient.mk I ⟨coeff p B n x, mem_plusSubring_iff.mp x.2 n⟩ := by
  simp [plusEquiv, coeffMonoidHom_plusMulEquiv]

/-- The zeroth coordinate of the inverse of `plusEquiv` is the Teichmüller map
`Perfection (B⁺ ⧸ I) p → B⁺`. -/
@[simp]
theorem coeff_zero_plusEquiv_symm (y : Perfection (Bplus ⧸ I) p) :
    coeff p B 0 ((plusEquiv h I).symm y : uniformTilt p B) = Perfection.teichmuller₀ p I y := by
  rw [plusEquiv_symm_apply, coeff_plusMulEquiv_symm,
    Perfection.coeff_zero_symm_quotientMulEquiv]

/-- Reduction identifies the integral tilt homeomorphically with the inverse limit of the
discrete quotients, whenever the topology on the ring of integral elements is `I`-adic. -/
theorem isHomeomorph_plusEquiv (hI : IsAdic I) :
    IsHomeomorph (plusEquiv h I : plusSubring p h → Perfection (Bplus ⧸ I) p) := by
  have hm : IsHomeomorph (plusMulEquiv h : plusSubring p h → Perfection Bplus p) := by
    refine (plusMulEquiv h).toEquiv.isHomeomorph_iff.mpr ⟨?_, ?_⟩
    · refine Perfection.continuous_iff.mpr fun n ↦ ?_
      exact ((continuous_coeff n).comp continuous_subtype_val).subtype_mk _
    · refine Continuous.subtype_mk (continuous_iff.mpr fun n ↦ ?_) _
      exact (continuous_subtype_val.comp (Perfection.continuous_coeffMonoidHom n)).congr
        fun y ↦ (coeff_plusMulEquiv_symm h y n).symm
  -- The underlying map of `plusEquiv` is the composite of the multiplicative equivalences.
  exact (Perfection.isHomeomorph_quotientMulEquiv hI).comp hm

end TauCeti.Perfectoid.uniformTilt

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Exponent
public import Mathlib.RingTheory.WittVector.TeichmullerSeries
public import TauCeti.RingTheory.WittVector.Truncated.Basic

/-!
# Witt vectors of an ideal

For an ideal `I` of a commutative ring `A`, the *Witt ideal* `W(I) ⊆ W(A)` is the kernel of
`W(A) → W(A ⧸ I)`: the Witt vectors all of whose coordinates lie in `I`. Its truncated analogue
`W_n(I) ⊆ W_n(A)` is the kernel of `W_n(A) → W_n(A ⧸ I)`. These are the sections over an affine
open of the Witt ideal sheaves `W I` and `W_n I` attached to a quasi-coherent ideal sheaf `I` of
a scheme of characteristic `p`, whose cohomology defines Witt vector cohomology with ideal
coefficients.

We record the characterizing API: membership is coordinatewise, the kernel of `W(f)` is the Witt
ideal of the kernel of `f` and its image is described coordinatewise, Witt ideals commute with
sums and intersections of ideals and are compatible with preimages and with images under
surjections, `W(A) ⧸ W(I) ≃ W(A ⧸ I)`, and the Witt ideal is stable under Teichmüller lifts of
`I`, Frobenius and Verschiebung. Truncation maps `W(I)` onto `W_n(I)` and `W_m(I)` onto `W_n(I)`
for `n ≤ m`, and the Witt vectors in `W(I)` whose first `n` coordinates vanish are exactly the
`V^n y` with `y ∈ W(I)`. These are the affine forms of the exact sequences of Witt ideal sheaves.

In characteristic `p` the Frobenius raises each coordinate to its `p`-th power and `V ∘ F = p`.
Hence if `a ^ p ^ c ∈ I` for every `a ∈ J`, then `F^c` and multiplication by `p ^ c` carry `W(J)`
into `W(I)` (`WittVector.mul_p_pow_mem_ideal`). For a nil ideal `N` of uniform exponent `p ^ c`,
for instance any ideal of a noetherian ring contained in the nilradical, `p ^ c` kills `W(N)`, so
`W(N)` has bounded `p`-power torsion. This is why rational Witt vector cohomology does not see
nilpotents.

## Main definitions

* `WittVector.ideal p I`: the Witt ideal `W(I) = ker (W(A) → W(A ⧸ I))`.
* `TruncatedWittVector.ideal p n I`: the truncated Witt ideal `W_n(I)`.
* `WittVector.quotientIdealEquiv p I`: the isomorphism `W(A) ⧸ W(I) ≃+* W(A ⧸ I)`, and its
  truncated analogue `TruncatedWittVector.quotientIdealEquiv p n I`.

## Main results

* `WittVector.mem_ideal_iff`: `x ∈ W(I)` iff every coordinate of `x` lies in `I`.
* `WittVector.ker_map`: the kernel of `W(f)` is `W(ker f)`.
* `WittVector.mem_range_map_iff`: a Witt vector lies in the image of `W(f)` iff every coordinate
  lies in the image of `f`.
* `WittVector.ideal_sup`, `WittVector.ideal_inf`: `W(I + J) = W(I) + W(J)` and
  `W(I ∩ J) = W(I) ∩ W(J)`.
* `TruncatedWittVector.ideal_sup`, `TruncatedWittVector.ideal_inf`: the same for `W_n`.
* `WittVector.mem_ideal_inf_ker_truncate_iff`: the elements of `W(I)` with vanishing first `n`
  coordinates are the `V^n y`, `y ∈ W(I)`.
* `TruncatedWittVector.map_wittVector_truncate_ideal`: truncation maps `W(I)` onto `W_n(I)`.
* `WittVector.mul_p_pow_mem_ideal`: in characteristic `p`, if `a ^ p ^ c ∈ I` for all `a ∈ J`,
  then `x * p ^ c ∈ W(I)` for all `x ∈ W(J)`.
* `WittVector.exponentExists_ideal`: in characteristic `p`, the Witt ideal of a nil ideal `N`
  with `a ^ p ^ c = 0` for all `a ∈ N` has an additive exponent.
* `WittVector.forall_mem_ideal_mul_p_pow_eq_zero_iff`: in characteristic `p`, `p ^ c` kills `W(N)`
  exactly when `a ^ p ^ c = 0` for all `a ∈ N`.

## References

* [P. Berthelot, S. Bloch, H. Esnault, *On Witt vector cohomology for singular varieties*,
  Compositio Math. 143 (2007)], §2, opening paragraphs, and Propositions 2.1 and 2.2 with their
  proofs.
* [A. Chatzistamatiou, K. Rülling, *Hodge–Witt cohomology and Witt-rational singularities*,
  Doc. Math. 17 (2012)], Lemma 4.6.2.
-/

public section

noncomputable section

namespace WittVector

variable (p : ℕ) [hp : Fact p.Prime] {A B : Type*} [CommRing A] [CommRing B]

@[inherit_doc] local notation "𝕎" => WittVector p

/-- The *Witt ideal* `W(I)` of an ideal `I ⊆ A`: the kernel of `W(A) → W(A ⧸ I)`, that is, the
Witt vectors all of whose coordinates lie in `I` (`WittVector.mem_ideal_iff`). -/
def ideal (I : Ideal A) : Ideal (𝕎 A) :=
  RingHom.ker (map (Ideal.Quotient.mk I))

variable {p}

/-- A Witt vector lies in the Witt ideal `W(I)` exactly when all of its coordinates lie in `I`. -/
theorem mem_ideal_iff {I : Ideal A} {x : 𝕎 A} : x ∈ ideal p I ↔ ∀ n, x.coeff n ∈ I := by
  simp only [ideal, RingHom.mem_ker, WittVector.ext_iff, map_coeff, zero_coeff,
    Ideal.Quotient.eq_zero_iff_mem]

/-- The kernel of the map of Witt vectors induced by a ring homomorphism `f` is the Witt ideal of
the kernel of `f`. -/
@[simp]
theorem ker_map (f : A →+* B) : RingHom.ker (map (p := p) f) = ideal p (RingHom.ker f) := by
  ext x
  simp only [RingHom.mem_ker, WittVector.ext_iff, map_coeff, zero_coeff, mem_ideal_iff]

/-- A Witt vector lies in the image of `WittVector.map f` if and only if each of its coordinates
lies in the image of `f`. -/
theorem mem_range_map_iff (f : A →+* B) (x : 𝕎 B) :
    x ∈ Set.range (map f) ↔ ∀ n, x.coeff n ∈ Set.range f := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨y, rfl⟩ n
    exact ⟨y.coeff n, (map_coeff f y n).symm⟩
  · choose c hc using h
    exact ⟨mk p c, ext fun n ↦ by rw [map_coeff, coeff_mk, hc]⟩

/-- The Witt ideal is monotone. -/
theorem ideal_mono {I J : Ideal A} (h : I ≤ J) : ideal p I ≤ ideal p J := fun _ hx ↦
  mem_ideal_iff.mpr fun n ↦ h (mem_ideal_iff.mp hx n)

/-- A Teichmüller representative `[a]` lies in `W(I)` exactly when `a ∈ I`. -/
@[simp]
theorem teichmuller_mem_ideal_iff {I : Ideal A} {a : A} : teichmuller p a ∈ ideal p I ↔ a ∈ I := by
  refine ⟨fun h ↦ teichmuller_coeff_zero p a ▸ mem_ideal_iff.mp h 0, fun ha ↦ ?_⟩
  refine mem_ideal_iff.mpr fun n ↦ ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · rwa [teichmuller_coeff_zero]
  · rw [teichmuller_coeff_pos p a n hn]
    exact I.zero_mem

/-- Witt ideals determine the ideals they come from. -/
@[simp]
theorem ideal_le_ideal_iff {I J : Ideal A} : ideal p I ≤ ideal p J ↔ I ≤ J :=
  ⟨fun h _ ha ↦ teichmuller_mem_ideal_iff.mp (h (teichmuller_mem_ideal_iff.mpr ha)), ideal_mono⟩

/-- Taking Witt ideals is injective. -/
theorem ideal_injective : Function.Injective (ideal p : Ideal A → Ideal (𝕎 A)) := fun _ _ h ↦
  le_antisymm (ideal_le_ideal_iff.mp h.le) (ideal_le_ideal_iff.mp h.ge)

/-- The Witt ideal of the zero ideal is zero. -/
@[simp]
theorem ideal_bot : ideal p (⊥ : Ideal A) = ⊥ := by
  ext x
  simp only [mem_ideal_iff, Ideal.mem_bot, WittVector.ext_iff, zero_coeff]

/-- The Witt ideal of the unit ideal is the unit ideal. -/
@[simp]
theorem ideal_top : ideal p (⊤ : Ideal A) = ⊤ := by
  ext x
  simp only [mem_ideal_iff, Submodule.mem_top, forall_const]

/-- Witt ideals commute with intersections. -/
@[simp]
theorem ideal_inf (I J : Ideal A) : ideal p (I ⊓ J) = ideal p I ⊓ ideal p J := by
  ext x
  simp only [mem_ideal_iff, Ideal.mem_inf, forall_and]

/-- Two Witt vectors are congruent modulo `W(I)` exactly when they are coordinatewise congruent
modulo `I`. -/
theorem sub_mem_ideal_iff {I : Ideal A} {x y : 𝕎 A} :
    x - y ∈ ideal p I ↔ ∀ n, x.coeff n - y.coeff n ∈ I := by
  simp only [ideal, RingHom.mem_ker, map_sub, sub_eq_zero, WittVector.ext_iff, map_coeff,
    Ideal.Quotient.eq]

/-- Witt ideals commute with sums: `W(I + J) = W(I) + W(J)`. Together with `WittVector.ideal_inf`
and the surjectivity of `W(A) → W(A ⧸ I)`, this gives the exactness of
`0 → W(A ⧸ I ∩ J) → W(A ⧸ I) × W(A ⧸ J) → W(A ⧸ (I + J)) → 0`. -/
@[simp]
theorem ideal_sup (I J : Ideal A) : ideal p (I ⊔ J) = ideal p I ⊔ ideal p J := by
  refine le_antisymm (fun x hx ↦ ?_) (sup_le (ideal_mono le_sup_left) (ideal_mono le_sup_right))
  have hx' n : ∃ a ∈ I, ∃ b ∈ J, a + b = x.coeff n :=
    Submodule.mem_sup.mp (mem_ideal_iff.mp hx n)
  choose a ha b hb hab using hx'
  refine Submodule.mem_sup.mpr ⟨mk p a, mem_ideal_iff.mpr ha, x - mk p a, ?_, add_sub_cancel _ _⟩
  refine sub_mem_ideal_iff.mpr fun n ↦ ?_
  rw [coeff_mk, ← hab, add_sub_cancel_left]
  exact hb n

/-- The preimage of a Witt ideal under `W(f)` is the Witt ideal of the preimage. -/
@[simp]
theorem comap_map_ideal (f : A →+* B) (J : Ideal B) :
    (ideal p J).comap (map f) = ideal p (J.comap f) := by
  ext x
  simp only [Ideal.mem_comap, mem_ideal_iff, map_coeff]

/-- The image of a Witt ideal under the map of Witt vectors induced by a surjection `f` is the
Witt ideal of the image. -/
theorem map_map_ideal_of_surjective (f : A →+* B) (hf : Function.Surjective f) (I : Ideal A) :
    (ideal p I).map (map f) = ideal p (I.map f) := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_) fun y hy ↦ ?_
  · simp only [Ideal.mem_comap, mem_ideal_iff, map_coeff] at hx ⊢
    exact fun n ↦ Ideal.mem_map_of_mem f (hx n)
  · have hy' n : ∃ a ∈ I, f a = y.coeff n :=
      (Ideal.mem_map_iff_of_surjective f hf).mp (mem_ideal_iff.mp hy n)
    choose a ha hfa using hy'
    have hmap : map f (mk p a) = y := by
      ext n
      simp only [map_coeff, hfa]
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ (mem_ideal_iff.mpr ha)

variable (p) in
/-- The Witt vectors of a quotient: `W(A) ⧸ W(I) ≃+* W(A ⧸ I)`, induced by `W(A) → W(A ⧸ I)`. -/
def quotientIdealEquiv (I : Ideal A) : 𝕎 A ⧸ ideal p I ≃+* 𝕎 (A ⧸ I) :=
  RingHom.quotientKerEquivOfSurjective (map_surjective _ Ideal.Quotient.mk_surjective)

/-- The isomorphism `W(A) ⧸ W(I) ≃+* W(A ⧸ I)` reduces every coordinate modulo `I`. -/
@[simp]
theorem quotientIdealEquiv_mk (I : Ideal A) (x : 𝕎 A) :
    quotientIdealEquiv p I (Ideal.Quotient.mk _ x) = map (Ideal.Quotient.mk I) x :=
  RingHom.quotientKerEquivOfSurjective_apply_mk _ x

/-- The Witt ideal is stable under the Witt vector Frobenius. -/
theorem frobenius_mem_ideal {I : Ideal A} {x : 𝕎 A} (hx : x ∈ ideal p I) :
    frobenius x ∈ ideal p I := by
  rw [ideal, RingHom.mem_ker] at hx ⊢
  rw [(frobenius_isPoly p).map, hx, map_zero]

/-- A Verschiebung `V x` lies in the Witt ideal `W(I)` exactly when `x` does. -/
@[simp]
theorem verschiebung_mem_ideal_iff {I : Ideal A} {x : 𝕎 A} :
    verschiebung x ∈ ideal p I ↔ x ∈ ideal p I := by
  simp only [mem_ideal_iff]
  refine ⟨fun h n ↦ verschiebung_coeff_succ x n ▸ h (n + 1), fun h n ↦ ?_⟩
  cases n with
  | zero => simpa only [verschiebung_coeff_zero] using I.zero_mem
  | succ n => simpa only [verschiebung_coeff_succ] using h n

/-- An iterated Verschiebung `V^n x` lies in `W(I)` exactly when `x` does. -/
@[simp]
theorem iterate_verschiebung_mem_ideal_iff {I : Ideal A} {x : 𝕎 A} (n : ℕ) :
    verschiebung^[n] x ∈ ideal p I ↔ x ∈ ideal p I := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', verschiebung_mem_ideal_iff, ih]

/-- The elements of `W(I)` whose first `n` Witt coordinates vanish are exactly the iterated
Verschiebungs `V^n y` of elements `y ∈ W(I)`. -/
theorem mem_ideal_inf_ker_truncate_iff {I : Ideal A} {x : 𝕎 A} (n : ℕ) :
    x ∈ ideal p I ⊓ RingHom.ker (truncate n) ↔ ∃ y ∈ ideal p I, verschiebung^[n] y = x := by
  rw [Submodule.mem_inf, mem_ker_truncate]
  constructor
  · rintro ⟨hx, hx0⟩
    refine ⟨x.shift n, mem_ideal_iff.mpr fun k ↦ ?_, (eq_iterate_verschiebung hx0).symm⟩
    rw [shift_coeff]
    exact mem_ideal_iff.mp hx _
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(iterate_verschiebung_mem_ideal_iff n).mpr hy,
      fun i hi ↦ iterate_verschiebung_coeff_eq_zero y hi⟩

/-- The zeroth coordinate maps the Witt ideal `W(I)` onto `I`. -/
@[simp]
theorem map_constantCoeff_ideal (I : Ideal A) : (ideal p I).map constantCoeff = I := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_) fun a ha ↦ ?_
  · exact mem_ideal_iff.mp hx 0
  · rw [← teichmuller_coeff_zero p a]
    exact Ideal.mem_map_of_mem constantCoeff (teichmuller_mem_ideal_iff.mpr ha)

section CharP

variable [CharP A p]

/-- In characteristic `p`, if `a ^ p ^ c ∈ I` for every `a ∈ J`, then the iterated Frobenius
`F^c` carries `W(J)` into `W(I)`. -/
theorem iterate_frobenius_mem_ideal {I J : Ideal A} {c : ℕ} (h : ∀ a ∈ J, a ^ p ^ c ∈ I)
    {x : 𝕎 A} (hx : x ∈ ideal p J) : frobenius^[c] x ∈ ideal p I :=
  mem_ideal_iff.mpr fun n ↦ iterate_frobenius_coeff x c n ▸ h _ (mem_ideal_iff.mp hx n)

/-- In characteristic `p`, if `a ^ p ^ c ∈ I` for every `a ∈ J`, then multiplication by `p ^ c`
carries `W(J)` into `W(I)`. -/
theorem mul_p_pow_mem_ideal {I J : Ideal A} {c : ℕ} (h : ∀ a ∈ J, a ^ p ^ c ∈ I)
    {x : 𝕎 A} (hx : x ∈ ideal p J) : x * (p : 𝕎 A) ^ c ∈ ideal p I := by
  rw [← iterate_verschiebung_iterate_frobenius, iterate_verschiebung_mem_ideal_iff]
  exact iterate_frobenius_mem_ideal h hx

/-- In characteristic `p`, if `a ^ p ^ c = 0` for every `a ∈ N`, then `p ^ c` kills the Witt
ideal `W(N)`. -/
theorem mul_p_pow_eq_zero_of_mem_ideal {N : Ideal A} {c : ℕ} (h : ∀ a ∈ N, a ^ p ^ c = 0)
    {x : 𝕎 A} (hx : x ∈ ideal p N) : x * (p : 𝕎 A) ^ c = 0 := by
  simpa only [ideal_bot, Ideal.mem_bot] using
    mul_p_pow_mem_ideal (I := ⊥) (fun a ha ↦ (Ideal.mem_bot).mpr (h a ha)) hx

/-- In characteristic `p`, the Witt ideal of a nil ideal of bounded exponent, one in which a
single power `a ^ p ^ c` of every element vanishes, has an additive exponent: one positive
integer kills all of `W(N)`. -/
theorem exponentExists_ideal {N : Ideal A} {c : ℕ} (h : ∀ a ∈ N, a ^ p ^ c = 0) :
    AddMonoid.ExponentExists (ideal p N) := by
  refine ⟨p ^ c, pow_pos hp.out.pos c, fun x ↦ Subtype.ext ?_⟩
  simpa [← Nat.cast_pow, Nat.cast_comm] using mul_p_pow_eq_zero_of_mem_ideal h x.property

/-- In characteristic `p`, `p ^ c` kills the Witt ideal `W(N)` exactly when `a ^ p ^ c = 0` for
every `a ∈ N`. -/
theorem forall_mem_ideal_mul_p_pow_eq_zero_iff {N : Ideal A} {c : ℕ} :
    (∀ x ∈ ideal p N, x * (p : 𝕎 A) ^ c = 0) ↔ ∀ a ∈ N, a ^ p ^ c = 0 := by
  refine ⟨fun h a ha ↦ ?_, fun h _ ↦ mul_p_pow_eq_zero_of_mem_ideal h⟩
  -- The `c`-th Witt coordinate of `[a] * p ^ c` is `a ^ p ^ c`.
  rw [← teichmuller_mul_pow_coeff, h _ (teichmuller_mem_ideal_iff.mpr ha), zero_coeff]

end CharP

end WittVector

namespace TruncatedWittVector

open WittVector

variable (p : ℕ) [hp : Fact p.Prime] {A B : Type*} [CommRing A] [CommRing B]

@[inherit_doc] local notation "𝕎" => WittVector p

/-- The *truncated Witt ideal* `W_n(I)` of an ideal `I ⊆ A`: the kernel of
`W_n(A) → W_n(A ⧸ I)`, that is, the truncated Witt vectors all of whose coordinates lie in `I`
(`TruncatedWittVector.mem_ideal_iff`). -/
def ideal (n : ℕ) (I : Ideal A) : Ideal (TruncatedWittVector p n A) :=
  RingHom.ker (map n (Ideal.Quotient.mk I))

variable {p}

/-- A truncated Witt vector lies in `W_n(I)` exactly when all of its coordinates lie in `I`. -/
@[simp]
theorem mem_ideal_iff {n : ℕ} {I : Ideal A} {x : TruncatedWittVector p n A} :
    x ∈ ideal p n I ↔ ∀ i, x.coeff i ∈ I := by
  simp only [ideal, RingHom.mem_ker, TruncatedWittVector.ext_iff, map_coeff, coeff_zero,
    Ideal.Quotient.eq_zero_iff_mem]

/-- The kernel of the map of truncated Witt vectors induced by `f` is the truncated Witt ideal of
the kernel of `f`. -/
@[simp]
theorem ker_map (n : ℕ) (f : A →+* B) :
    RingHom.ker (map (p := p) n f) = ideal p n (RingHom.ker f) := by
  ext x
  simp only [RingHom.mem_ker, TruncatedWittVector.ext_iff, map_coeff, coeff_zero, mem_ideal_iff]

/-- Two truncated Witt vectors are congruent modulo `W_n(I)` exactly when they are
coordinatewise congruent modulo `I`. -/
theorem sub_mem_ideal_iff {n : ℕ} {I : Ideal A} {x y : TruncatedWittVector p n A} :
    x - y ∈ ideal p n I ↔ ∀ i, x.coeff i - y.coeff i ∈ I := by
  simp only [ideal, RingHom.mem_ker, map_sub, sub_eq_zero, TruncatedWittVector.ext_iff,
    map_coeff, Ideal.Quotient.eq]

/-- The preimage of a truncated Witt ideal under `W_n(f)` is the truncated Witt ideal of the
preimage. -/
@[simp]
theorem comap_map_ideal (n : ℕ) (f : A →+* B) (J : Ideal B) :
    (ideal p n J).comap (map n f) = ideal p n (J.comap f) := by
  ext x
  simp only [Ideal.mem_comap, mem_ideal_iff, map_coeff]

variable (p) in
/-- The truncated Witt vectors of a quotient: `W_n(A) ⧸ W_n(I) ≃+* W_n(A ⧸ I)`. -/
def quotientIdealEquiv (n : ℕ) (I : Ideal A) :
    TruncatedWittVector p n A ⧸ ideal p n I ≃+* TruncatedWittVector p n (A ⧸ I) :=
  RingHom.quotientKerEquivOfSurjective (map_surjective n _ Ideal.Quotient.mk_surjective)

/-- The isomorphism `W_n(A) ⧸ W_n(I) ≃+* W_n(A ⧸ I)` reduces every coordinate modulo `I`. -/
@[simp]
theorem quotientIdealEquiv_mk (n : ℕ) (I : Ideal A) (x : TruncatedWittVector p n A) :
    quotientIdealEquiv p n I (Ideal.Quotient.mk _ x) = map n (Ideal.Quotient.mk I) x :=
  RingHom.quotientKerEquivOfSurjective_apply_mk _ x

/-- Truncation `W(A) → W_n(A)` maps the Witt ideal `W(I)` onto the truncated Witt ideal
`W_n(I)`. -/
@[simp]
theorem map_wittVector_truncate_ideal (n : ℕ) (I : Ideal A) :
    (WittVector.ideal p I).map (WittVector.truncate n) = ideal p n I := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_) fun y hy ↦ ?_
  · simp only [Ideal.mem_comap, mem_ideal_iff, WittVector.coeff_truncate]
    exact fun i ↦ WittVector.mem_ideal_iff.mp hx i
  · have hy' : WittVector.truncate n y.out = y := truncateFun_out y
    rw [← hy']
    refine Ideal.mem_map_of_mem _ (WittVector.mem_ideal_iff.mpr fun k ↦ ?_)
    rcases lt_or_ge k n with hk | hk
    · exact coeff_out y ⟨k, hk⟩ ▸ mem_ideal_iff.mp hy ⟨k, hk⟩
    · rw [coeff_out_eq_zero_of_le y hk]
      exact I.zero_mem

/-- For `m ≤ n`, truncation `W_n(A) → W_m(A)` maps `W_n(I)` onto `W_m(I)`. -/
@[simp]
theorem map_truncate_ideal {m n : ℕ} (hm : m ≤ n) (I : Ideal A) :
    (ideal p n I).map (truncate hm) = ideal p m I := by
  rw [← map_wittVector_truncate_ideal, Ideal.map_map, truncate_comp_wittVector_truncate,
    map_wittVector_truncate_ideal]

/-- The image of a truncated Witt ideal under the map of truncated Witt vectors induced by a
surjection `f` is the truncated Witt ideal of the image. -/
theorem map_map_ideal_of_surjective (n : ℕ) (f : A →+* B) (hf : Function.Surjective f)
    (I : Ideal A) : (ideal p n I).map (map n f) = ideal p n (I.map f) := by
  have hcomp : (map n f).comp (WittVector.truncate n) =
      (WittVector.truncate (p := p) n).comp (WittVector.map f) :=
    RingHom.ext (map_wittVector_truncate n f)
  rw [← map_wittVector_truncate_ideal, Ideal.map_map, hcomp, ← Ideal.map_map,
    WittVector.map_map_ideal_of_surjective f hf, map_wittVector_truncate_ideal]

/-- The truncated Witt ideal is monotone. -/
theorem ideal_mono {n : ℕ} {I J : Ideal A} (h : I ≤ J) : ideal p n I ≤ ideal p n J :=
  fun _ hx ↦ mem_ideal_iff.mpr fun i ↦ h (mem_ideal_iff.mp hx i)

/-- The truncated Witt ideal of the zero ideal is zero. -/
@[simp]
theorem ideal_bot (n : ℕ) : ideal p n (⊥ : Ideal A) = ⊥ := by
  ext x
  simp only [mem_ideal_iff, Ideal.mem_bot, TruncatedWittVector.ext_iff, coeff_zero]

/-- The truncated Witt ideal of the unit ideal is the unit ideal. -/
@[simp]
theorem ideal_top (n : ℕ) : ideal p n (⊤ : Ideal A) = ⊤ := by
  ext x
  simp only [mem_ideal_iff, Submodule.mem_top, implies_true]

/-- Truncated Witt ideals commute with intersections. -/
@[simp]
theorem ideal_inf (n : ℕ) (I J : Ideal A) : ideal p n (I ⊓ J) = ideal p n I ⊓ ideal p n J := by
  ext x
  simp only [mem_ideal_iff, Ideal.mem_inf, forall_and]

/-- Truncated Witt ideals commute with sums: `W_n(I + J) = W_n(I) + W_n(J)`. -/
@[simp]
theorem ideal_sup (n : ℕ) (I J : Ideal A) : ideal p n (I ⊔ J) = ideal p n I ⊔ ideal p n J := by
  simp only [← map_wittVector_truncate_ideal, WittVector.ideal_sup, Ideal.map_sup]

end TruncatedWittVector

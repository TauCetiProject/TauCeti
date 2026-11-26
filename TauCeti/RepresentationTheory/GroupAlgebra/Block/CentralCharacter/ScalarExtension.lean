/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Basic
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.CenterMap
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.CentralCharacter

/-!
# Blocks with a central character stay blocks under scalar extension

Let `k ⊆ k'` be fields, `G` a finite group and `e_B` a block idempotent of `k[G]` with a central
character, a `k`-algebra homomorphism `λ_B : Z(k[G]) → k` with `λ_B(e_B) = 1`; every block has one
when `k` splits `G`. Then the image of `e_B` in `k'[G]` is again a block idempotent.

The local ring `Z(k[G]) e_B` is Artinian with residue field `k` through `λ_B`, so its maximal
ideal, the elements `x e_B` with `λ_B(x) = 0`, consists of nilpotent elements
(`TauCeti.IsPrimitiveIdempotent.isNilpotent_mul_of_apply_eq_zero`). The class sums `K_C` span both
centres, so every element of `Z(k'[G]) e_B` is `c e_B + m` with `c ∈ k'` and `m` a `k'`-linear
combination of the nilpotent elements `K_C e_B - λ_B(K_C) e_B`, hence nilpotent. An idempotent of
this form has `(c² - c) e_B` nilpotent, so `c ∈ {0, 1}`, and it is then `0` or `e_B`, since
idempotents differing by a nilpotent element are equal. This is the step of the scalar extension
of ModularCharactersAndBlocks §6.2 that the blocks of `k[G]` stay blocks of `k'[G]` when `k`
splits `G`.

Without the central character this fails: along `𝔽₂ ⊆ 𝔽₄` the block `r + r²` of `𝔽₂[C₃]`, which
has none, splits into two blocks of `𝔽₄[C₃]`
(`TauCeti.GroupAlgebraBlockExamples.not_isBlockIdempotent_centerMapRingHom_r_add_r_sq`).

## Main results

* `TauCeti.IsPrimitiveIdempotent.isNilpotent_mul_of_apply_eq_zero`: for a primitive idempotent
  `e` of a commutative Artinian `k`-algebra and a `k`-algebra homomorphism `φ` with `φ(e) = 1`,
  `x e` is nilpotent whenever `φ(x) = 0`.
* `IsIdempotentElem.eq_zero_or_eq_of_eq_algebraMap_mul_add`: an idempotent `c β + m`, with `β` a
  nonzero idempotent and `m` nilpotent with `m β = m`, is `0` or `β`.
* `TauCeti.IsPrimitiveIdempotent.isPrimitiveIdempotent_map_of_span_eq_top`: such an `e` stays
  primitive under a ring homomorphism, compatible with a field homomorphism `k → k'`, whose image
  spans the target over `k'`.
* `TauCeti.IsBlockIdempotent.isBlockIdempotent_centerMapRingHom`: a block idempotent of `k[G]`
  with a central character maps to a block idempotent of `k'[G]` along every field homomorphism
  `k → k'`; `TauCeti.IsBlockIdempotent.isBlockIdempotent_centerMapRingHom_of_isAlgClosed` for
  `k` algebraically closed, where every block has a central character.
-/

public section

namespace TauCeti

section Nilpotent

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] [IsArtinianRing A] {e : A}

/-- **The maximal ideal of a local corner is nil.** Let `e` be a primitive idempotent of a
commutative Artinian `k`-algebra `A` and `φ : A → k` a `k`-algebra homomorphism with `φ(e) = 1`.
If `φ(x) = 0`, then `x e` is nilpotent: by the Artinian property `x^n = x^(n+1) y` for some `n`
and `y`, and `(1 - x y) e` is invertible in the local ring `eA`, so `x^n e = 0`. -/
theorem IsPrimitiveIdempotent.isNilpotent_mul_of_apply_eq_zero (he : IsPrimitiveIdempotent e)
    {φ : A →ₐ[k] k} (hφ : φ e = 1) {x : A} (hx : φ x = 0) : IsNilpotent (x * e) := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : A)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
  obtain ⟨z, hz⟩ := (he.exists_mul_mul_eq_or (x * y)).resolve_left fun ⟨z, hz⟩ => by
    have := congrArg φ hz
    rw [map_mul, map_mul, map_mul, hx, zero_mul, zero_mul, zero_mul, hφ] at this
    exact zero_ne_one this
  have hxn : x ^ n * e = 0 := by
    calc x ^ n * e = x ^ n * ((1 - x * y) * z * e) := by rw [hz]
      _ = (x ^ n - x ^ (n + 1) * y) * z * e := by ring
      _ = 0 := by rw [hy, sub_self, zero_mul, zero_mul]
  refine ⟨n + 1, ?_⟩
  rw [mul_pow, he.isIdempotentElem.pow_succ_eq, pow_succ', mul_assoc, hxn, mul_zero]

omit [IsArtinianRing A] in
/-- **Idempotents of a corner with nilpotent radical.** In a commutative `K`-algebra `A`, let `β`
be a nonzero idempotent and `e` an idempotent of the form `e = c β + m` with `c ∈ K`, `m`
nilpotent and `m β = m`. Then `e` is `0` or `β`: `(c² - c) β = m (1 - 2c - m)` is nilpotent, so
`c² = c`, and idempotents differing by a nilpotent element are equal. -/
theorem _root_.IsIdempotentElem.eq_zero_or_eq_of_eq_algebraMap_mul_add {K : Type*} [Field K]
    [Algebra K A] {β e m : A} (hβ : IsIdempotentElem β) (hβ0 : β ≠ 0) (he : IsIdempotentElem e)
    {c : K} (hm : IsNilpotent m) (hmβ : m * β = m) (he' : e = algebraMap K A c * β + m) :
    e = 0 ∨ e = β := by
  -- An idempotent nilpotent element is `0`.
  have hzero (x : A) (hx : IsIdempotentElem x) (hxn : IsNilpotent x) : x = 0 := by
    obtain ⟨N, hN⟩ := hxn
    rw [← hx.pow_succ_eq N, pow_succ, hN, zero_mul]
  have hcβ : IsNilpotent (algebraMap K A (c * c - c) * β) := by
    have hsq : algebraMap K A (c * c - c) * β = m * (1 - 2 * algebraMap K A c - m) := by
      have := he.eq
      rw [he'] at this
      rw [map_sub, map_mul]
      linear_combination this - (algebraMap K A c) ^ 2 * hβ.eq - 2 * algebraMap K A c * hmβ
    rw [hsq]
    exact (Commute.all _ _).isNilpotent_mul_right hm
  have hc : c * c - c = 0 := by
    by_contra hc
    refine hβ0 (hzero β hβ ?_)
    have hβ' : β = algebraMap K A (c * c - c)⁻¹ * (algebraMap K A (c * c - c) * β) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rw [hβ']
    exact (Commute.all _ _).isNilpotent_mul_left hcβ
  have hc' : c * (c - 1) = 0 := by linear_combination hc
  rcases mul_eq_zero.1 hc' with h0 | h1
  · -- `c = 0`: `e = m` is nilpotent.
    left
    refine hzero e he ?_
    rwa [he', h0, map_zero, zero_mul, zero_add]
  · -- `c = 1`: `e - β = m` is nilpotent.
    right
    refine eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute he hβ ?_ (Commute.all _ _)
    rwa [he', sub_eq_zero.1 h1, map_one, one_mul, add_sub_cancel_left]

/-- **Primitivity survives a map whose image spans.** Let `e` be a primitive idempotent of a
commutative Artinian `k`-algebra `A` with a `k`-algebra homomorphism `φ : A → k`, `φ(e) = 1`, and
`F : A → A'` a ring homomorphism to a commutative `k'`-algebra, compatible with a field
homomorphism `f : k → k'`, whose image spans `A'` over `k'`. If `F e ≠ 0`, then `F e` is
primitive: every element of `F(e) A'` is `c F(e) + m` with `m` nilpotent, since
`F(e) F(a) = f(φ(a)) F(e) + F(a e - φ(a) e)` and `a e - φ(a) e` is nilpotent. -/
theorem IsPrimitiveIdempotent.isPrimitiveIdempotent_map_of_span_eq_top {k' A' : Type*} [Field k']
    [CommRing A'] [Algebra k' A'] (he : IsPrimitiveIdempotent e) {φ : A →ₐ[k] k} (hφ : φ e = 1)
    (f : k →+* k') (F : A →+* A') (hF : ∀ r, F (algebraMap k A r) = algebraMap k' A' (f r))
    (hspan : Submodule.span k' (Set.range F) = ⊤) (h0 : F e ≠ 0) :
    IsPrimitiveIdempotent (F e) := by
  have hβ : IsIdempotentElem (F e) := he.isIdempotentElem.map F
  have key (y : A') : ∃ (c : k') (m : A'), IsNilpotent m ∧ m * F e = m ∧
      F e * y = algebraMap k' A' c * F e + m := by
    have hy : y ∈ Submodule.span k' (Set.range F) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      refine ⟨f (φ a), F (a * e - algebraMap k A (φ a) * e), ?_, ?_, ?_⟩
      · have := he.isNilpotent_mul_of_apply_eq_zero hφ (x := a - algebraMap k A (φ a)) (by simp)
        rw [sub_mul] at this
        exact this.map F
      · rw [← map_mul, sub_mul, mul_assoc, mul_assoc, he.isIdempotentElem.eq]
      · rw [map_sub, map_mul, map_mul, hF]
        ring
    | zero => exact ⟨0, 0, IsNilpotent.zero, zero_mul _, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, m, hm, hmβ, hy⟩ := hy
      obtain ⟨d, n, hn, hnβ, hz⟩ := hz
      refine ⟨c + d, m + n, (Commute.all _ _).isNilpotent_add hm hn, by rw [add_mul, hmβ, hnβ], ?_⟩
      rw [mul_add, hy, hz, map_add]
      ring
    | smul r y _ hy =>
      obtain ⟨c, m, hm, hmβ, hy⟩ := hy
      refine ⟨r * c, r • m, hm.smul r, by rw [smul_mul_assoc, hmβ], ?_⟩
      rw [mul_smul_comm, hy, smul_add, map_mul, Algebra.smul_def, Algebra.smul_def]
      ring
  refine isPrimitiveIdempotent_of_eq_zero_or_eq hβ h0 fun x hx hβx _ => ?_
  obtain ⟨c, m, hm, hmβ, hxc⟩ := key x
  rw [hβx] at hxc
  exact hβ.eq_zero_or_eq_of_eq_algebraMap_mul_add h0 hx hm hmβ hxc

end Nilpotent

open _root_.MonoidAlgebra

variable {k k' G : Type*} [Field k] [Field k'] [Group G] [Finite G]

/-- **Blocks with a central character stay blocks.** Let `f : k →+* k'` be a homomorphism of
fields, `G` a finite group, and `e_B` a block idempotent of `k[G]` with a central character
`φ : Z(k[G]) → k`, `φ(e_B) = 1`. Then the image of `e_B` in `k'[G]` is a block idempotent. -/
theorem IsBlockIdempotent.isBlockIdempotent_centerMapRingHom (f : k →+* k')
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b)
    {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k} (hφ : φ b = 1) :
    IsBlockIdempotent (centerMapRingHom G f b) := by
  classical
  have := Fintype.ofFinite G
  refine IsPrimitiveIdempotent.isPrimitiveIdempotent_map_of_span_eq_top hb hφ f
    (centerMapRingHom G f) (centerMapRingHom_algebraMap G f) ?_ fun h => hb.ne_zero ?_
  · -- The class sums of `k'[G]` span its centre, and they are images of class sums.
    rw [eq_top_iff, ← (classSumBasis (k := k') (G := G)).span_eq, Submodule.span_le]
    rintro _ ⟨C, rfl⟩
    exact Submodule.subset_span
      ⟨classSumCenter C, by rw [classSumBasis_apply, centerMapRingHom_classSumCenter]⟩
  · exact Subtype.ext <| mapRingHom_injective f.injective <| by
      simpa using congrArg Subtype.val h

/-- **Blocks over an algebraically closed field stay blocks.** For `k` algebraically closed and
`f : k →+* k'` a homomorphism of fields, the image of a block idempotent of `k[G]` in `k'[G]` is a
block idempotent: its central character exists. -/
theorem IsBlockIdempotent.isBlockIdempotent_centerMapRingHom_of_isAlgClosed [IsAlgClosed k]
    (f : k →+* k') {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b) :
    IsBlockIdempotent (centerMapRingHom G f b) :=
  hb.isBlockIdempotent_centerMapRingHom f hb.centralCharacter_self

end TauCeti

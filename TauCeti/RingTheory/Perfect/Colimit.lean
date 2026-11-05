/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Algebra.CharP.Frobenius.PowRingHom
public import TauCeti.RingTheory.Perfect.IsPRadical

/-!
# The colimit perfection of a ring in which `p` vanishes

Let `p` be a prime and `A` a commutative ring with `p = 0`. The *colimit perfection* of `A` is the
direct limit `A → A → A → ⋯` along the `p`-th power map `x ↦ x ^ p`. Writing `mk n x` for the class
of `x` in the `n`-th copy, it is the element `x ^ (1 / p ^ n)`: its `p ^ n`-th power is
`of x = mk 0 x`. The map `of : A → ColimitPerfection A p hA` is `p`-radical, its target is perfect,
and every ring map from `A` to a perfect ring extends uniquely along it.

This is the construction of Mathlib's `PerfectClosure A p`, to which it is isomorphic when `A` has
characteristic `p` (`TauCeti.ColimitPerfection.ringEquivPerfectClosure`). Mathlib's version needs
`CharP A p`, which the zero ring does not satisfy. The colimit perfection only asks that `p`
vanish, so it is defined on every ring of sections of a scheme over `𝔽_p`, including the zero ring
of sections over the empty open. It commutes with localization
(`TauCeti.ColimitPerfection.isLocalization_away`): this is what makes
`U ↦ ColimitPerfection Γ(X, U)` glue, over the affine opens `U` of a scheme `X` over `𝔽_p`, to the
perfection of `X`.

## Main definitions

* `TauCeti.ColimitPerfection A p hA`: the colimit perfection of `A`, for `hA : (p : A) = 0`.
* `TauCeti.ColimitPerfection.mk A p hA n`: the inclusion of the `n`-th copy of `A`, so that
  `mk A p hA n x` is the `p ^ n`-th root of `of A p hA x`.
* `TauCeti.ColimitPerfection.of A p hA`: the canonical map `A →+* ColimitPerfection A p hA`.
* `TauCeti.ColimitPerfection.lift`: the extension of a ring map into a perfect ring.
* `TauCeti.ColimitPerfection.map`: functoriality in ring maps.
* `TauCeti.ColimitPerfection.ringEquivPerfectClosure`: the comparison with Mathlib's
  `PerfectClosure A p` for rings of characteristic `p`.

## Main results

* `TauCeti.ColimitPerfection.mk_eq_mk_iff`: `mk n x = mk n y` iff `x ^ p ^ k = y ^ p ^ k` for some
  `k`.
* `TauCeti.ColimitPerfection.perfectRing`: the colimit perfection is a perfect ring.
* `TauCeti.ColimitPerfection.isPRadical`: the map `of` is `p`-radical.
* `TauCeti.ColimitPerfection.bijective_of`: a perfect ring is its own colimit perfection.
* `TauCeti.ColimitPerfection.isLocalization_away`: the colimit perfection of the localization
  `A[1 / f]` is the localization of the colimit perfection of `A` away from `of f`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), Definition 3.1 and Lemma 3.4.
-/

public noncomputable section

namespace TauCeti

variable (A : Type*) [CommRing A] (p : ℕ) [hp : Fact p.Prime] (hA : (p : A) = 0)

/-- The transition maps `x ↦ x ^ p ^ (n - m)` of the direct system defining the colimit
perfection. -/
def ColimitPerfection.transition (m n : ℕ) (_ : m ≤ n) : A →+* A :=
  powRingHom A p hA ^ (n - m)

theorem ColimitPerfection.transition_apply {m n : ℕ} (h : m ≤ n) (x : A) :
    transition A p hA m n h x = x ^ p ^ (n - m) := by
  rw [transition, RingHom.coe_pow, funext (powRingHom_apply hA)]
  exact congrFun (pow_iterate p (n - m)) x

instance ColimitPerfection.directedSystem :
    DirectedSystem (fun _ : ℕ ↦ A) (transition A p hA · · ·) where
  map_self x := by simp [transition_apply]
  map_map {k j i} hij hjk x := by
    simp only [transition_apply, ← pow_mul, ← pow_add]
    congr 2
    omega

/-- The *colimit perfection* of a ring `A` in which the prime `p` vanishes: the direct limit of
`A → A → A → ⋯` along the `p`-th power map. Unlike Mathlib's `PerfectClosure A p`, it does not
require `CharP A p`, and so it is defined for the zero ring. It is an abbreviation so that it
inherits the ring structure of the direct limit. -/
abbrev ColimitPerfection : Type _ :=
  DirectLimit (fun _ : ℕ ↦ A) (ColimitPerfection.transition A p hA)

namespace ColimitPerfection

/-- The inclusion of the `n`-th copy of `A` in its colimit perfection: `mk A p hA n x` is the
`p ^ n`-th root of `of A p hA x`. -/
def mk (n : ℕ) : A →+* ColimitPerfection A p hA :=
  DirectLimit.Ring.of (fun _ : ℕ ↦ A) (transition A p hA) n

/-- The canonical map from `A` to its colimit perfection. -/
def of : A →+* ColimitPerfection A p hA :=
  mk A p hA 0

@[simp]
theorem mk_zero_eq_of : mk A p hA 0 = of A p hA :=
  (rfl)

variable {A p hA}

/-- Every element of the colimit perfection is the image of some `x` in some copy of `A`. -/
theorem exists_eq_mk (z : ColimitPerfection A p hA) : ∃ (n : ℕ) (x : A), z = mk A p hA n x :=
  DirectLimit.exists_eq_mk _ z

/-- Two elements of the colimit perfection come from the same copy of `A`. -/
theorem exists_eq_mk₂ (z w : ColimitPerfection A p hA) :
    ∃ (n : ℕ) (x y : A), z = mk A p hA n x ∧ w = mk A p hA n y :=
  DirectLimit.exists_eq_mk₂ _ z w

/-- The class of `x ^ p ^ k` in the `(n + k)`-th copy of `A` is the class of `x` in the `n`-th
copy. -/
@[simp]
theorem mk_add_apply_pow_pow (n k : ℕ) (x : A) :
    mk A p hA (n + k) (x ^ p ^ k) = mk A p hA n x := by
  have h := DirectLimit.Ring.of_f (G := fun _ : ℕ ↦ A) (f := transition A p hA)
    (Nat.le_add_right n k) x
  rwa [transition_apply, Nat.add_sub_cancel_left] at h

theorem mk_succ_apply_pow (n : ℕ) (x : A) : mk A p hA (n + 1) (x ^ p) = mk A p hA n x := by
  simpa using mk_add_apply_pow_pow (hA := hA) n 1 x

theorem of_eq_mk (n : ℕ) (x : A) : of A p hA x = mk A p hA n (x ^ p ^ n) := by
  have h := mk_add_apply_pow_pow (hA := hA) 0 n x
  rw [zero_add] at h
  rw [h, mk_zero_eq_of]

/-- The `p ^ n`-th power of `mk n x` is `of x`. -/
@[simp]
theorem mk_pow_pow (n : ℕ) (x : A) : mk A p hA n x ^ p ^ n = of A p hA x := by
  rw [← map_pow, ← of_eq_mk]

/-- The `p`-th power of `mk (n + 1) x` is `mk n x`. -/
@[simp]
theorem mk_succ_pow (n : ℕ) (x : A) : mk A p hA (n + 1) x ^ p = mk A p hA n x := by
  rw [← map_pow, mk_succ_apply_pow]

/-- **Equality in the colimit perfection.** Two elements of the same copy of `A` agree in the
colimit perfection exactly when they agree after raising to some power `p ^ k`. -/
theorem mk_eq_mk_iff {n : ℕ} {x y : A} :
    mk A p hA n x = mk A p hA n y ↔ ∃ k : ℕ, x ^ p ^ k = y ^ p ^ k := by
  refine ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · obtain ⟨i, hx, hy, hxy⟩ := Quotient.eq.1 h
    exact ⟨i - n, by simpa only [transition_apply] using hxy⟩
  · rw [← mk_add_apply_pow_pow n k x, ← mk_add_apply_pow_pow n k y, hk]

theorem mk_eq_zero_iff {n : ℕ} {x : A} : mk A p hA n x = 0 ↔ ∃ k : ℕ, x ^ p ^ k = 0 := by
  rw [← map_zero (mk A p hA n), mk_eq_mk_iff]
  simp [zero_pow (pow_ne_zero _ hp.out.ne_zero)]

theorem of_eq_zero_iff {x : A} : of A p hA x = 0 ↔ ∃ k : ℕ, x ^ p ^ k = 0 :=
  mk_eq_zero_iff

/-- The prime `p` vanishes in the colimit perfection. -/
theorem natCast_eq_zero : (p : ColimitPerfection A p hA) = 0 := by
  rw [← map_natCast (of A p hA), hA, map_zero]

variable (A p hA)

/-- **The colimit perfection is a perfect ring**: the `p`-th root of `mk n x` is `mk (n + 1) x`,
and `p`-th powers are injective because equality is tested after raising to powers of `p`. -/
instance perfectRing : PerfectRing (ColimitPerfection A p hA) p where
  bijective_frobenius := by
    refine ⟨fun z w h ↦ ?_, fun z ↦ ?_⟩
    · obtain ⟨n, x, y, rfl, rfl⟩ := exists_eq_mk₂ z w
      simp only [← map_pow] at h
      obtain ⟨k, hk⟩ := mk_eq_mk_iff.1 h
      exact mk_eq_mk_iff.2 ⟨k + 1, by rw [pow_succ', pow_mul, pow_mul, hk]⟩
    · obtain ⟨n, x, rfl⟩ := exists_eq_mk z
      exact ⟨mk A p hA (n + 1) x, mk_succ_pow n x⟩

/-- **The map from a ring to its colimit perfection is `p`-radical**: a power `p ^ n` of each
element comes from `A`, and the kernel consists of `p`-nilpotent elements. -/
instance isPRadical : IsPRadical (of A p hA) p where
  pow_mem' z := by
    obtain ⟨n, x, rfl⟩ := exists_eq_mk z
    exact ⟨n, x, (mk_pow_pow n x).symm⟩
  ker_le' x hx := by
    obtain ⟨k, hk⟩ := of_eq_zero_iff.1 (RingHom.mem_ker.1 hx)
    exact mem_pNilradical.2 ⟨k, hk⟩

/-- **A perfect ring is its own colimit perfection**: when the `p`-th power map of `A` is
bijective, so is the map from `A` to its colimit perfection. -/
theorem bijective_of [PerfectRing A p] : Function.Bijective (of A p hA) := by
  have hF := PerfectRing.bijective_frobenius (R := A) (p := p)
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨k, hk⟩ := of_eq_zero_iff.1 hx
    refine hF.1.iterate k ?_
    rw [pow_iterate]
    simpa [zero_pow (pow_ne_zero _ hp.out.ne_zero)] using hk
  · obtain ⟨n, x, rfl⟩ := exists_eq_mk z
    obtain ⟨y, hy⟩ := hF.2.iterate n x
    rw [pow_iterate] at hy
    exact ⟨y, (of_eq_mk n y).trans (congrArg _ hy)⟩

/-! ### The universal property -/

section Lift

variable {M : Type*} [CommRing M] [PerfectRing M p]

/-- **The universal property of the colimit perfection**: ring maps from the colimit perfection of
`A` to a perfect ring `M` are determined by their restriction to `A`, and every ring map `A →+* M`
arises this way. The ring `M` may be the zero ring. -/
theorem bijective_comp_of :
    Function.Bijective fun g : ColimitPerfection A p hA →+* M ↦ g.comp (of A p hA) :=
  IsPRadical.bijective_comp (of A p hA) p hA

variable {A p hA}

/-- Ring maps from the colimit perfection to a perfect ring agree once they agree on `A`. -/
theorem hom_ext {g₁ g₂ : ColimitPerfection A p hA →+* M}
    (h : g₁.comp (of A p hA) = g₂.comp (of A p hA)) : g₁ = g₂ :=
  (bijective_comp_of A p hA).1 h

variable (hA) in
/-- The extension of a ring map `g : A →+* M` to a perfect ring `M` along the map from `A` to its
colimit perfection. -/
def lift (g : A →+* M) : ColimitPerfection A p hA →+* M :=
  (Equiv.ofBijective _ (bijective_comp_of A p hA (M := M))).symm g

@[simp]
theorem lift_comp_of (g : A →+* M) : (lift hA g).comp (of A p hA) = g :=
  (Equiv.ofBijective _ (bijective_comp_of A p hA (M := M))).apply_symm_apply g

@[simp]
theorem lift_of (g : A →+* M) (x : A) : lift hA g (of A p hA x) = g x :=
  RingHom.congr_fun (lift_comp_of g) x

/-- The extension of `g` sends `mk n x`, the `p ^ n`-th root of `x`, to the `p ^ n`-th root of
`g x`. -/
theorem lift_mk_pow_pow (g : A →+* M) (n : ℕ) (x : A) :
    lift hA g (mk A p hA n x) ^ p ^ n = g x := by
  rw [← map_pow, mk_pow_pow, lift_of]

theorem lift_unique (g : A →+* M) (h : ColimitPerfection A p hA →+* M)
    (hh : h.comp (of A p hA) = g) : h = lift hA g :=
  hom_ext (hh.trans (lift_comp_of g).symm)

end Lift

/-! ### Functoriality -/

section Map

variable {A p hA} {B C : Type*} [CommRing B] [CommRing C]

variable (hA) in
/-- The map of colimit perfections induced by a ring map `g : A →+* B`; it sends the class of `x`
in the `n`-th copy of `A` to the class of `g x` in the `n`-th copy of `B`. -/
def map (hB : (p : B) = 0) (g : A →+* B) : ColimitPerfection A p hA →+* ColimitPerfection B p hB :=
  DirectLimit.Ring.lift (fun _ : ℕ ↦ A) (transition A p hA) _ (fun n ↦ (mk B p hB n).comp g)
    fun m n hmn x ↦ by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    simp [transition_apply]

@[simp]
theorem map_mk (hB : (p : B) = 0) (g : A →+* B) (n : ℕ) (x : A) :
    map hA hB g (mk A p hA n x) = mk B p hB n (g x) :=
  (rfl)

@[simp]
theorem map_of (hB : (p : B) = 0) (g : A →+* B) (x : A) :
    map hA hB g (of A p hA x) = of B p hB (g x) :=
  (rfl)

theorem map_comp_of (hB : (p : B) = 0) (g : A →+* B) :
    (map hA hB g).comp (of A p hA) = (of B p hB).comp g :=
  (rfl)

/-- The map induced by `g` is the extension of `of ∘ g`. -/
theorem map_eq_lift (hB : (p : B) = 0) (g : A →+* B) :
    map hA hB g = lift hA ((of B p hB).comp g) :=
  lift_unique _ _ (map_comp_of hB g)

@[simp]
theorem map_id : map hA hA (RingHom.id A) = RingHom.id (ColimitPerfection A p hA) :=
  hom_ext (by ext; simp)

theorem map_comp (hB : (p : B) = 0) (hC : (p : C) = 0) (g : A →+* B) (h : B →+* C) :
    map hA hC (h.comp g) = (map hB hC h).comp (map hA hB g) :=
  hom_ext (by ext; simp)

theorem map_map (hB : (p : B) = 0) (hC : (p : C) = 0) (g : A →+* B) (h : B →+* C)
    (z : ColimitPerfection A p hA) : map hB hC h (map hA hB g z) = map hA hC (h.comp g) z := by
  rw [map_comp hB hC]
  rfl

end Map

/-! ### Localization -/

section Localization

variable {A p hA} {A' : Type*} [CommRing A'] [Algebra A A'] (f : A) [IsLocalization.Away f A']

/-- In a localization `A'` of `A` away from `f`, a relation `f ^ m * a ^ p ^ k = 0` between
elements of `A` becomes the vanishing of `mk n a` after multiplying by a power of `of f`. -/
private theorem of_pow_mul_mk_eq_zero {n k m : ℕ} {a : A} (h : f ^ m * a ^ p ^ k = 0) :
    of A p hA (f ^ m) * mk A p hA n a = 0 := by
  rw [of_eq_mk n, ← map_mul, mk_eq_zero_iff]
  refine ⟨k, ?_⟩
  obtain ⟨e, he⟩ : ∃ e, p ^ (n + k) = e + 1 :=
    Nat.exists_eq_add_one.2 (pow_pos hp.out.pos _)
  calc ((f ^ m) ^ p ^ n * a) ^ p ^ k = (f ^ m) ^ p ^ (n + k) * a ^ p ^ k := by
        rw [mul_pow, ← pow_mul, ← pow_add]
    _ = (f ^ m) ^ e * (f ^ m * a ^ p ^ k) := by rw [he, pow_succ, mul_assoc]
    _ = 0 := by rw [h, mul_zero]

variable (hA' : (p : A') = 0)

/-- **The colimit perfection commutes with localization.** If `A'` is the localization of `A` away
from `f`, then the colimit perfection of `A'` is the localization of the colimit perfection of `A`
away from `of f`. -/
theorem isLocalization_away :
    letI := (map hA hA' (algebraMap A A')).toAlgebra
    IsLocalization.Away (of A p hA f) (ColimitPerfection A' p hA') := by
  let := (map hA hA' (algebraMap A A')).toAlgebra
  have halg (z : ColimitPerfection A p hA) :
      algebraMap (ColimitPerfection A p hA) (ColimitPerfection A' p hA') z =
        map hA hA' (algebraMap A A') z := (rfl)
  refine IsLocalization.Away.mk _ ?_ (fun z ↦ ?_) (fun z w hzw ↦ ?_)
  · rw [halg, map_of]
    exact (IsLocalization.Away.algebraMap_isUnit f).map _
  · -- Write `z = mk n a'` with `a' * f ^ k = a`; then `z * (of f) ^ k = mk n (a * f ^ (k * e))`,
    -- where `p ^ n = e + 1`.
    obtain ⟨n, a', rfl⟩ := exists_eq_mk z
    obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj f a'
    obtain ⟨e, he⟩ : ∃ e, p ^ n = e + 1 := Nat.exists_eq_add_one.2 (pow_pos hp.out.pos _)
    refine ⟨k, mk A p hA n (a * f ^ (k * e)), ?_⟩
    rw [halg, halg, map_of, map_mk, of_eq_mk n, ← map_pow, ← map_mul]
    congr 1
    rw [map_mul, map_pow, ← ha, he]
    ring
  · -- Reduce to the vanishing of `z - w = mk n a` after mapping to `A'`.
    rw [← sub_eq_zero, ← map_sub] at hzw
    obtain ⟨n, a, ha⟩ := exists_eq_mk (z - w)
    rw [ha, halg, map_mk, mk_eq_zero_iff] at hzw
    obtain ⟨k, hk⟩ := hzw
    rw [← map_pow, IsLocalization.map_eq_zero_iff (Submonoid.powers f)] at hk
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := hk
    refine ⟨m, ?_⟩
    rw [← sub_eq_zero, ← mul_sub, ha, ← map_pow]
    exact of_pow_mul_mk_eq_zero f hm

end Localization

/-! ### Comparison with `PerfectClosure` -/

section PerfectClosure

variable [CharP A p]

/-- For a ring `A` of characteristic `p`, the colimit perfection of `A` is Mathlib's
`PerfectClosure A p`, compatibly with the maps from `A`. -/
def ringEquivPerfectClosure : ColimitPerfection A p hA ≃+* PerfectClosure A p :=
  let e := Equiv.ofBijective _ (IsPRadical.bijective_comp (PerfectClosure.of A p) p hA
    (M := ColimitPerfection A p hA))
  have he : (e.symm (of A p hA)).comp (PerfectClosure.of A p) = of A p hA :=
    e.apply_symm_apply (of A p hA)
  RingEquiv.ofRingHom (lift hA (PerfectClosure.of A p)) (e.symm (of A p hA))
    ((IsPRadical.bijective_comp (PerfectClosure.of A p) p hA).1 <| by
      dsimp only
      rw [RingHom.comp_assoc, he, lift_comp_of, RingHom.id_comp])
    (hom_ext <| by rw [RingHom.comp_assoc, lift_comp_of, he, RingHom.id_comp])

@[simp]
theorem ringEquivPerfectClosure_of (x : A) :
    ringEquivPerfectClosure A p hA (of A p hA x) = PerfectClosure.of A p x :=
  lift_of _ x

end PerfectClosure

end ColimitPerfection

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import TauCeti.RingTheory.AdicCompletion.Pow

/-!
# Adic formal smoothness

`Algebra.AdicFormallySmooth` tests square-zero lifting against discrete rings, expressing
continuity by vanishing on an ideal power. Its `lift_adic` theorem uses
`IsAdicComplete.liftAlgHom` to extend lifting to complete adic test rings
(Stacks Project, Definition 15.38.3 and Lemma 15.38.5).
-/

public section

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {C D : Type max u v} [CommRing C] [Semiring D] [Algebra R C] [Algebra R D]

/-- Formal smoothness of `S` over `R` in the `K`-adic topology, tested against discrete rings.
In a square-zero lifting problem, continuity of a lift follows from continuity modulo the
square-zero ideal. See the Stacks Project, Definition 15.38.3 (07NI). -/
@[stacks 07NI, mk_iff]
structure AdicFormallySmooth (K : Ideal S) : Prop where
  /-- A map to a discrete square-zero quotient that kills a power of `K` admits a lift. -/
  exists_lift {C : Type max u v} [CommRing C] [Algebra R C] (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (f : S →ₐ[R] C ⧸ J) (hf : ∃ m : ℕ, K ^ m ≤ RingHom.ker f.toRingHom) :
    ∃ g : S →ₐ[R] C, (Ideal.Quotient.mkₐ R J).comp g = f

namespace AdicFormallySmooth

open Ideal

variable {K : Ideal S}

/-- A map that kills a power of `K` lifts along a surjection with square-zero kernel and the lift
also kills a power of `K`. This is the surjection form of Stacks Project, Definition 15.38.3. -/
theorem exists_lift_of_surjective (h : AdicFormallySmooth (R := R) K)
    (q : C →ₐ[R] D) (hq : Function.Surjective q) (hker : RingHom.ker q.toRingHom ^ 2 = ⊥)
    (f : S →ₐ[R] D) (hf : ∃ m : ℕ, K ^ m ≤ RingHom.ker f.toRingHom) :
    ∃ g : S →ₐ[R] C, q.comp g = f ∧ ∃ m : ℕ, K ^ m ≤ RingHom.ker g.toRingHom := by
  obtain ⟨m, hm⟩ := hf
  let e := Ideal.quotientKerAlgEquivOfSurjective hq
  have hf' : K ^ m ≤ RingHom.ker (e.symm.toAlgHom.comp f).toRingHom := fun x hx ↦ by
    have hx₀ : f x = 0 := hm hx
    exact (congrArg e.symm hx₀).trans (map_zero _)
  obtain ⟨g, hg⟩ := h.exists_lift _ hker (e.symm.toAlgHom.comp f) ⟨m, hf'⟩
  have heq : q.comp g = f := AlgHom.ext fun x ↦
    (congrArg e (AlgHom.congr_fun hg x)).trans (e.apply_symm_apply (f x))
  have hmap : (K ^ m).map g.toRingHom ≤ RingHom.ker q.toRingHom :=
    map_le_iff_le_comap.mpr fun x hx ↦ (AlgHom.congr_fun heq x).trans (hm hx)
  refine ⟨g, heq, ⟨m * 2, (map_eq_bot_iff_le_ker _).mp ?_⟩⟩
  rw [pow_mul, Ideal.map_pow]
  exact le_bot_iff.mp ((pow_right_mono hmap 2).trans hker.le)

/-- Lift a compatible pair of maps to two quotients through a square-zero extension of their
fiber product, provided both maps kill powers of `K`. -/
theorem exists_lift_of_quotient_pair (h : AdicFormallySmooth (R := R) K)
    {A B L : Ideal C} (hLA : L ≤ A) (hLB : L ≤ B) (hL : (A ⊓ B) ^ 2 ≤ L)
    (g : S →ₐ[R] C ⧸ A) (f : S →ₐ[R] C ⧸ B)
    (hcomp : (Quotient.factorₐ R le_sup_left).comp g = (Quotient.factorₐ R le_sup_right).comp f)
    (hg : ∃ m : ℕ, K ^ m ≤ RingHom.ker g.toRingHom)
    (hf : ∃ m : ℕ, K ^ m ≤ RingHom.ker f.toRingHom) :
    ∃ l : S →ₐ[R] C ⧸ L, (Quotient.factorₐ R hLA).comp l = g ∧
      (Quotient.factorₐ R hLB).comp l = f ∧ ∃ m : ℕ, K ^ m ≤ RingHom.ker l.toRingHom := by
  let p := (Quotient.factorₐ R (le_sup_left : A ≤ A ⊔ B)).comp (AlgHom.fst R (C ⧸ A) (C ⧸ B))
  let q := (Quotient.factorₐ R (le_sup_right : B ≤ A ⊔ B)).comp (AlgHom.snd R (C ⧸ A) (C ⧸ B))
  let a : C ⧸ L →ₐ[R] AlgHom.equalizer p q :=
    ((Quotient.factorₐ R hLA).prod (Quotient.factorₐ R hLB)).codRestrict _
      (Ideal.Quotient.mk_surjective.forall.mpr fun x ↦
        (AlgHom.mem_equalizer _ _ _).mpr (by simp [p, q]))
  have ha : Function.Surjective a := by
    rintro ⟨⟨x, y⟩, hxy⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hsub := Ideal.Quotient.eq.mp ((AlgHom.mem_equalizer p q _).mp hxy)
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hsub
    refine ⟨Ideal.Quotient.mk _ (x - i), Subtype.ext (Prod.ext (Ideal.Quotient.eq.mpr ?_)
      (Ideal.Quotient.eq.mpr ?_))⟩
    · simpa only [sub_sub_cancel_left] using A.neg_mem hi
    · have heq : x - i - y = j := by linear_combination -hij
      rwa [heq]
  have hker : RingHom.ker a.toRingHom ≤ (A ⊓ B).map (Ideal.Quotient.mk L) := by
    intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hz' : a (Ideal.Quotient.mk L x) = 0 := hz
    have ⟨hA, hB⟩ : Ideal.Quotient.mk A x = 0 ∧ Ideal.Quotient.mk B x = 0 :=
      Prod.ext_iff.mp (congrArg Subtype.val hz')
    exact mem_map_of_mem _ ⟨Quotient.eq_zero_iff_mem.mp hA, Quotient.eq_zero_iff_mem.mp hB⟩
  let b : S →ₐ[R] AlgHom.equalizer p q :=
    (g.prod f).codRestrict _ fun x ↦ (AlgHom.mem_equalizer _ _ _).mpr (AlgHom.congr_fun hcomp x)
  obtain ⟨m, hm⟩ := hg
  obtain ⟨n, hn⟩ := hf
  have hb : K ^ max m n ≤ RingHom.ker b.toRingHom := fun x hx ↦
    Subtype.ext (Prod.ext (hm (pow_le_pow_right (le_max_left _ _) hx))
      (hn (pow_le_pow_right (le_max_right _ _) hx)))
  have hsq : RingHom.ker a.toRingHom ^ 2 = ⊥ := by
    apply le_bot_iff.mp ((pow_right_mono hker 2).trans ?_)
    rw [← Ideal.map_pow, map_le_iff_le_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact hL
  obtain ⟨l, hl, hl'⟩ := h.exists_lift_of_surjective a ha hsq b ⟨_, hb⟩
  exact ⟨l, AlgHom.ext fun x ↦ congrArg (fun z ↦ z.val.1) (AlgHom.congr_fun hl x),
    AlgHom.ext fun x ↦ congrArg (fun z ↦ z.val.2) (AlgHom.congr_fun hl x), hl'⟩

/-- Construct compatible lifts to the powers of an ideal containing the prescribed kernel. -/
theorem exists_compatible_lifts (h : AdicFormallySmooth (R := R) K)
    {H J : Ideal C} (hJH : J ≤ H) (f : S →ₐ[R] C ⧸ J)
    (hf : ∀ n : ℕ, ∃ m : ℕ, K ^ m ≤ RingHom.ker
      ((Quotient.factorₐ R (le_sup_right : J ≤ H ^ n ⊔ J)).comp f).toRingHom) :
    ∃ g : (n : ℕ) → S →ₐ[R] C ⧸ H ^ n,
      (∀ {a b : ℕ} (hab : a ≤ b),
        (Quotient.factorₐ R (pow_le_pow_right hab)).comp (g b) = g a) ∧
      ∀ n, (Quotient.factorₐ R (le_sup_left : H ^ n ≤ H ^ n ⊔ J)).comp (g n) =
        (Quotient.factorₐ R le_sup_right).comp f ∧
        ∃ m : ℕ, K ^ m ≤ RingHom.ker (g n).toRingHom := by
  let L (n : ℕ) := {g : S →ₐ[R] C ⧸ H ^ n //
    (Quotient.factorₐ R (le_sup_left : H ^ n ≤ H ^ n ⊔ J)).comp g =
      (Quotient.factorₐ R le_sup_right).comp f ∧ ∃ m : ℕ, K ^ m ≤ RingHom.ker g.toRingHom}
  have : Subsingleton (C ⧸ H ^ 0) := by simp
  have : Subsingleton (C ⧸ (H ^ 0 ⊔ J)) := by simp
  have start : L 0 := ⟨default, Subsingleton.elim _ _, ⟨0, fun _ _ ↦ Subsingleton.elim _ _⟩⟩
  have step (n : ℕ) (g : L n) : ∃ l : L (n + 1),
      (Quotient.factorₐ R (pow_le_pow_right n.le_succ)).comp l.val = g.val := by
    have hpow : H ^ (n + 1) ≤ H ^ n := pow_le_pow_right n.le_succ
    have hs : H ^ n ⊔ J ≤ H ^ n ⊔ (H ^ (n + 1) ⊔ J) :=
      sup_le le_sup_left (le_sup_right.trans le_sup_right)
    have hcomp := congrArg ((Quotient.factorₐ R hs).comp) g.property.1
    have hsq : (H ^ n ⊓ (H ^ (n + 1) ⊔ J)) ^ 2 ≤ H ^ (n + 1) := by
      by_cases hn : n = 0
      · subst n
        simpa only [pow_zero, zero_add, pow_one, one_eq_top, top_inf_eq, sup_eq_left.mpr hJH]
          using (pow_le_pow_right (I := H) (Nat.le_succ 1))
      · refine (pow_right_mono inf_le_left 2).trans ?_
        rw [← pow_mul]
        exact pow_le_pow_right (by omega)
    obtain ⟨l, hl, hred, hkill⟩ := h.exists_lift_of_quotient_pair hpow le_sup_left hsq g.val
      ((Quotient.factorₐ R le_sup_right).comp f)
      (by simpa only [← AlgHom.comp_assoc, Quotient.factorₐ_comp] using hcomp)
      g.property.2 (hf (n + 1))
    exact ⟨⟨l, hred, hkill⟩, hl⟩
  let levels : (n : ℕ) → L n := Nat.rec start fun n g ↦ (step n g).choose
  refine ⟨fun n ↦ (levels n).val, ?_, fun n ↦ (levels n).property⟩
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hs := (step b (levels b)).choose_spec
    rw [← Quotient.factorₐ_comp R (pow_le_pow_right b.le_succ)
      (pow_le_pow_right hab), AlgHom.comp_assoc, hs, ih]

/-- A continuous map into the quotient of an `I`-adically complete test ring by a closed ideal
`J` lifts continuously if a power of `J` lies in `I`. The infimum equality expresses closedness.
See the Stacks Project, Lemma 15.38.5 (07NJ). -/
@[stacks 07NJ]
theorem lift_adic (h : AdicFormallySmooth (R := R) K)
    (I J : Ideal C) [IsAdicComplete I C] (hJ : (⨅ n : ℕ, I ^ n ⊔ J) = J)
    (hJI : ∃ t : ℕ, J ^ t ≤ I) (f : S →ₐ[R] C ⧸ J)
    (hf : ∀ n : ℕ, ∃ m : ℕ, K ^ m ≤ RingHom.ker
      ((Quotient.factorₐ R (le_sup_right : J ≤ I ^ n ⊔ J)).comp f).toRingHom) :
    ∃ g : S →ₐ[R] C, (Quotient.mkₐ R J).comp g = f ∧
      ∀ n : ℕ, ∃ m : ℕ, K ^ m ≤ (I ^ n).comap g.toRingHom := by
  obtain ⟨t, ht⟩ := hJI
  let H := I ⊔ J
  let : IsAdicComplete H C := IsAdicComplete.sup_of_pow_le ht
  have hHI : H ^ (1 + t) ≤ I := sup_pow_add_le_pow_sup_pow.trans (sup_le (pow_one I).le ht)
  have hcofinal (n : ℕ) : H ^ ((1 + t) * n) ≤ I ^ n := by
    rw [pow_mul]
    exact pow_right_mono hHI _
  obtain ⟨levels, compat, hlevels⟩ := h.exists_compatible_lifts (H := H) le_sup_right f fun n ↦ by
    obtain ⟨m, hm⟩ := hf n
    have hle : I ^ n ⊔ J ≤ H ^ n ⊔ J := sup_le_sup (pow_right_mono le_sup_left _) le_rfl
    refine ⟨m, fun x hx ↦ ?_⟩
    have hzero : Quotient.factorₐ R (le_sup_right : J ≤ I ^ n ⊔ J) (f x) = 0 := hm hx
    have he := congr(($(Quotient.factorₐ_comp R le_sup_right hle)) (f x))
    exact he.symm.trans (by rw [AlgHom.comp_apply, hzero, map_zero])
  let g := IsAdicComplete.liftAlgHom H levels compat
  have hred (n : ℕ) (x : S) : Ideal.Quotient.mk (H ^ n) (g x) = levels n x :=
    IsAdicComplete.mk_liftAlgHom H _ compat n x
  refine ⟨g, AlgHom.ext fun x ↦ ?_, fun n ↦ ?_⟩
  · obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (f x)
    rw [AlgHom.comp_apply, Quotient.mkₐ_eq_mk, ← hy, Ideal.Quotient.eq, ← hJ]
    refine Ideal.mem_iInf.mpr fun n ↦ sup_le_sup (hcofinal n) le_rfl (Ideal.Quotient.eq.mp ?_)
    simpa only [AlgHom.comp_apply, ← hred ((1 + t) * n) x, ← hy, Quotient.factorₐ_apply_mk]
      using AlgHom.congr_fun (hlevels ((1 + t) * n)).1 x
  · obtain ⟨m, hm⟩ := (hlevels ((1 + t) * n)).2
    exact ⟨m, fun x hx ↦ hcofinal n (Quotient.eq_zero_iff_mem.mp ((hred _ x).trans (hm hx)))⟩

end AdicFormallySmooth
end Algebra

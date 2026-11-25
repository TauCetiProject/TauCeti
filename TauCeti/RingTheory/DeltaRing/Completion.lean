/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Algebra
public import TauCeti.RingTheory.AdicCompletion.AlgHom
public import TauCeti.RingTheory.DeltaRing.Basic

/-!
# The `δ`-structure on an adic completion

Let `A` be a `δ`-ring and `I` an ideal of `A` containing `p`. The `δ`-operation is not additive
and does not preserve `I`, but it loses exactly one power of `I`: if `x ∈ I ^ (n + 1)` then
`δ x ∈ I ^ n`, and more generally `δ x - δ y ∈ I ^ n` whenever `x - y ∈ I ^ (n + 1)`. Hence `δ`
descends to functions `A ⧸ I ^ (n + 1) → A ⧸ I ^ n`, compatible with the transition maps, and
passes to the inverse limit: the `I`-adic completion `AdicCompletion I A` carries a `δ`-structure
for which the canonical map `A → AdicCompletion I A` is a map of `δ`-rings. No finiteness
hypothesis on `I` is needed for the construction. When `I` is finitely generated this is the only
`δ`-structure on the completion compatible with the canonical map.

Nothing here assumes that `p` is prime, that `A` is `p`-torsion free, or that `A` is `I`-adically
separated.

## Main definitions and results

* `TauCeti.DeltaRing.delta_mem_pow_of_mem_pow_succ`: if `p ∈ I` and `x ∈ I ^ (n + 1)`, then
  `δ x ∈ I ^ n`.
* `TauCeti.DeltaRing.delta_sub_delta_mem_pow`: if `p ∈ I` and `x - y ∈ I ^ (n + 1)`, then
  `δ x - δ y ∈ I ^ n`.
* `TauCeti.DeltaRing.quotientDelta`: the function `A ⧸ I ^ (n + 1) → A ⧸ I ^ n` induced by `δ`,
  with its compatibility with the transition maps `TauCeti.DeltaRing.factorPow_quotientDelta`.
* `TauCeti.DeltaRing.adicCompletion`: the `δ`-structure on `AdicCompletion I A`, characterised
  by `TauCeti.DeltaRing.evalₐ_delta_adicCompletion`, and compatible with the canonical map
  (`TauCeti.DeltaRing.delta_adicCompletion_algebraMap`).
* `TauCeti.DeltaRing.eq_adicCompletion`: for finitely generated `I`, every `δ`-structure on the
  completion compatible with the canonical map is `TauCeti.DeltaRing.adicCompletion`.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  Lemma 2.17.
-/

public section

namespace TauCeti

namespace DeltaRing

open AdicCompletion

variable {p : ℕ} {A : Type*} [CommRing A] [DeltaRing p A] {I : Ideal A}

section Ideal

/-- If `p ∈ I`, then `δ` sends `I ^ (n + 1)` into `I ^ n` (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Lemma 2.17). The loss of one power is sharp: in `ℤ` with `I = (p)`,
`δ (p ^ (n + 1))` has `p`-adic valuation exactly `n`. -/
theorem delta_mem_pow_of_mem_pow_succ (hp : (p : A) ∈ I) {n : ℕ} {x : A}
    (hx : x ∈ I ^ (n + 1)) : delta p x ∈ I ^ n := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [delta_eq_zero_of_p_eq_zero rfl]
    exact zero_mem _
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ'] at hx
    induction hx using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      rw [delta_mul]
      refine add_mem (add_mem ?_ ?_) ?_
      · rw [pow_succ']
        exact Ideal.mul_mem_mul (I.pow_mem_of_mem ha p (Nat.pos_of_ne_zero hp0)) (ih hb)
      · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hb p (Nat.pos_of_ne_zero hp0))
      · rw [mul_assoc, pow_succ']
        exact Ideal.mul_mem_mul hp (Ideal.mul_mem_left _ _ (ih hb))
    | add x hx y hy hx' hy' =>
      rw [delta_add]
      exact add_mem (add_mem hx' hy') (addCorrection_mem_of_mem_left y (Ideal.mul_le_right hx))

/-- If `p ∈ I` and `x ≡ y` modulo `I ^ (n + 1)`, then `δ x ≡ δ y` modulo `I ^ n`
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Lemma 2.17): `δ` is uniformly continuous
for the `I`-adic topology, with modulus `n + 1`. -/
theorem delta_sub_delta_mem_pow (hp : (p : A) ∈ I) {n : ℕ} {x y : A}
    (h : x - y ∈ I ^ (n + 1)) : delta p x - delta p y ∈ I ^ n := by
  have e := delta_add (p := p) (x - y) y
  rw [sub_add_cancel] at e
  rw [e, add_right_comm, add_sub_cancel_right]
  exact add_mem (delta_mem_pow_of_mem_pow_succ hp h)
    (Ideal.pow_le_pow_right n.le_succ (addCorrection_mem_of_mem_left y h))

end Ideal

section Quotient

/-- For `p ∈ I`, the function `A ⧸ I ^ (n + 1) → A ⧸ I ^ n` sending the class of `a` to the class
of `δ a`; it is well defined by `delta_sub_delta_mem_pow`. It is neither additive nor
multiplicative. -/
def quotientDelta (hp : (p : A) ∈ I) (n : ℕ) : A ⧸ I ^ (n + 1) → A ⧸ I ^ n :=
  Quotient.lift (fun a ↦ Ideal.Quotient.mk (I ^ n) (delta p a)) fun _ _ h ↦
    Ideal.Quotient.eq.mpr <| delta_sub_delta_mem_pow hp <| Ideal.Quotient.eq.mp <| Quotient.sound h

/-- `quotientDelta` sends the class of `a` to the class of `δ a`. -/
@[simp]
theorem quotientDelta_mk (hp : (p : A) ∈ I) (n : ℕ) (a : A) :
    quotientDelta hp n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (delta p a) :=
  (rfl)

/-- `quotientDelta` sends `0` to `0`, since `δ 0 = 0`. -/
@[simp]
theorem quotientDelta_zero (hp : (p : A) ∈ I) (n : ℕ) : quotientDelta hp n 0 = 0 := by
  rw [← _root_.map_zero (Ideal.Quotient.mk (I ^ (n + 1))), quotientDelta_mk, delta_zero,
    _root_.map_zero]

/-- The functions `quotientDelta` are compatible with the transition maps of the `I`-adic
quotients. -/
theorem factorPow_quotientDelta (hp : (p : A) ∈ I) {m n : ℕ} (h : m ≤ n)
    (z : A ⧸ I ^ (n + 1)) :
    Ideal.Quotient.factorPow I h (quotientDelta hp n z) =
      quotientDelta hp m (Ideal.Quotient.factorPow I (Nat.succ_le_succ h) z) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp

end Quotient

section Completion

/-- The `δ`-operation on the completion, on a chosen adic Cauchy sequence representing the input:
its `n`-th term is `δ` of the `(n + 1)`-st term of the input sequence. -/
private noncomputable def completionDelta (hp : (p : A) ∈ I) (x : AdicCompletion I A) :
    AdicCompletion I A :=
  let f := Function.surjInv (mk_surjective I A) x
  AdicCompletion.mk I A <| AdicCauchySequence.mk I A (fun n ↦ delta p (f (n + 1))) fun n ↦ by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact delta_sub_delta_mem_pow hp <| by
      simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using f.property (Nat.le_succ (n + 1))

private theorem evalₐ_completionDelta (hp : (p : A) ∈ I) (n : ℕ) (x : AdicCompletion I A) :
    evalₐ I n (completionDelta hp x) = quotientDelta hp n (evalₐ I (n + 1) x) := by
  conv_rhs => rw [← Function.surjInv_eq (mk_surjective I A) x]
  simp [completionDelta]

private theorem evalₐ_completionDelta_of_evalₐ_eq (hp : (p : A) ∈ I) {n : ℕ}
    {x : AdicCompletion I A} {a : A} (h : evalₐ I (n + 1) x = Ideal.Quotient.mk _ a) :
    evalₐ I n (completionDelta hp x) = Ideal.Quotient.mk _ (delta p a) := by
  rw [evalₐ_completionDelta, h, quotientDelta_mk]

/-- The `δ`-structure on the `I`-adic completion of a `δ`-ring `A`, for an ideal `I` containing
`p` (Bhatt and Scholze, *Prisms and prismatic cohomology*, Lemma 2.17). The image of `δ x` in
`A ⧸ I ^ n` is `δ` of a lift of the image of `x` in `A ⧸ I ^ (n + 1)`
(`evalₐ_delta_adicCompletion`), and the canonical map `A → AdicCompletion I A` commutes with `δ`
(`delta_adicCompletion_algebraMap`). The ideal `I` need not be finitely generated; when it is,
this is the only such `δ`-structure (`eq_adicCompletion`). -/
@[instance_reducible]
noncomputable def adicCompletion (hp : (p : A) ∈ I) : DeltaRing p (AdicCompletion I A) where
  delta := completionDelta hp
  delta_zero := ext_evalₐ fun n ↦ by simp [evalₐ_completionDelta]
  delta_one := ext_evalₐ fun n ↦ by
    rw [evalₐ_completionDelta_of_evalₐ_eq hp (n := n) (a := 1) (by simp)]
    simp
  delta_add x y := ext_evalₐ fun n ↦ by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I (n + 1) x)
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ I (n + 1) y)
    rw [evalₐ_completionDelta_of_evalₐ_eq hp (a := a + b) (by simp [ha, hb]), delta_add]
    simp only [map_add, map_addCorrection,
      evalₐ_completionDelta_of_evalₐ_eq hp ha.symm, evalₐ_completionDelta_of_evalₐ_eq hp hb.symm,
      evalₐ_eq_mk_of_le n.le_succ ha.symm, evalₐ_eq_mk_of_le n.le_succ hb.symm]
  delta_mul x y := ext_evalₐ fun n ↦ by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I (n + 1) x)
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ I (n + 1) y)
    rw [evalₐ_completionDelta_of_evalₐ_eq hp (a := a * b) (by simp [ha, hb]), delta_mul]
    simp only [map_add, map_mul, map_pow, map_natCast,
      evalₐ_completionDelta_of_evalₐ_eq hp ha.symm, evalₐ_completionDelta_of_evalₐ_eq hp hb.symm,
      evalₐ_eq_mk_of_le n.le_succ ha.symm, evalₐ_eq_mk_of_le n.le_succ hb.symm]

/-- The image of `δ x` in `A ⧸ I ^ n` is `quotientDelta` of the image of `x` in
`A ⧸ I ^ (n + 1)`. In particular it only depends on the image of `x` in `A ⧸ I ^ (n + 1)`. -/
@[simp]
theorem evalₐ_delta_adicCompletion (hp : (p : A) ∈ I) (n : ℕ) (x : AdicCompletion I A) :
    evalₐ I n ((adicCompletion hp).delta x) = quotientDelta hp n (evalₐ I (n + 1) x) :=
  evalₐ_completionDelta hp n x

/-- The image of `δ x` in `A ⧸ I ^ n` only depends on the image of `x` in `A ⧸ I ^ (n + 1)`. -/
theorem evalₐ_delta_adicCompletion_eq_of_evalₐ_eq (hp : (p : A) ∈ I) {n : ℕ}
    {x y : AdicCompletion I A} (h : evalₐ I (n + 1) x = evalₐ I (n + 1) y) :
    evalₐ I n ((adicCompletion hp).delta x) = evalₐ I n ((adicCompletion hp).delta y) := by
  simp [h]

/-- The canonical map `A → AdicCompletion I A` is a map of `δ`-rings. -/
@[simp]
theorem delta_adicCompletion_algebraMap (hp : (p : A) ∈ I) (a : A) :
    (adicCompletion hp).delta (algebraMap A (AdicCompletion I A) a) =
      algebraMap A (AdicCompletion I A) (delta p a) :=
  ext_evalₐ fun n ↦ by simp [evalₐ_delta_adicCompletion]

/-- For a finitely generated ideal `I` containing `p`, every `δ`-structure on `AdicCompletion I A`
for which the canonical map from `A` commutes with `δ` is `adicCompletion` (Bhatt and Scholze,
*Prisms and prismatic cohomology*, Lemma 2.17). -/
theorem eq_adicCompletion (fg : I.FG) (hp : (p : A) ∈ I) (d : DeltaRing p (AdicCompletion I A))
    (hd : ∀ a, d.delta (algebraMap A (AdicCompletion I A) a) =
      algebraMap A (AdicCompletion I A) (delta p a)) :
    d = adicCompletion hp := by
  refine DeltaRing.ext (funext fun x ↦ ext_evalₐ fun n ↦ ?_)
  -- Approximate `x` by the image of some `a : A` modulo the `(n + 1)`-st power of `I`.
  obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_map_pow fg (n + 1) x
  have hp' : (p : AdicCompletion I A) ∈ I.map (algebraMap A (AdicCompletion I A)) := by
    simpa using Ideal.mem_map_of_mem (algebraMap A (AdicCompletion I A)) hp
  -- The continuity of `d` makes `d.delta x` congruent to `δ a` modulo the `n`-th power of `I`.
  let := d
  have hd' := delta_sub_delta_mem_pow hp' (n := n) (by rwa [← Ideal.map_pow])
  rw [hd, ← Ideal.map_pow, ← ker_evalₐ_eq_map_pow fg, RingHom.mem_ker, map_sub, sub_eq_zero]
    at hd'
  rw [← ker_evalₐ_eq_map_pow fg, RingHom.mem_ker, map_sub, sub_eq_zero] at ha
  simp [hd', ha]

end Completion

end DeltaRing

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.SixJ

/-!
# The quantum Biedenharn–Elliott pentagon identity

On a quadruple tensor product `L_a^ε ⊗ L_b^δ ⊗ L_c^ζ ⊗ L_d^θ` of signed ladder modules of
`U_q(sl₂)`, Mac Lane's pentagon identity (`BialgebraModule.assoc_pentagon`) equates the two
reassociation paths from the left-comb parenthesization `((L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ) ⊗ L_d^θ` to
the right-comb parenthesization `L_a^ε ⊗ (L_b^δ ⊗ (L_c^ζ ⊗ L_d^θ))`:

1. the two-step path `(assoc A B (C ⊗ D)) ∘ (assoc (A ⊗ B) C D)` through `(A ⊗ B) ⊗ (C ⊗ D)`;
2. the three-step path `(id_A ⊗ assoc B C D) ∘ (assoc A (B ⊗ C) D) ∘ (assoc A B C ⊗ id_D)`
   through `(A ⊗ (B ⊗ C)) ⊗ D` and `A ⊗ ((B ⊗ C) ⊗ D)`.

At a generic quantum parameter `q`, expanding both paths on a left-comb Clebsch–Gordan channel
`(p, q', e)` via `assoc_comp_clebschGordanWeightInclusion` and naturality of `BialgebraModule.assoc`
(`tensorMap_tensorMap_comp_assoc_eq`), then extracting the `(r, s, e)` right-comb coordinate via
`quadrupleRightProjection` and `LadderModule.homScalar`, yields the quantum **Biedenharn–Elliott
pentagon identity** (`biedenharn_elliott`):

`∑_{t = 0}^{b + c} 6j(b, c, d, s; t, r) * 6j(a, t, d, e; q', s) * 6j(a, b, c, q'; p, t) =`
`  6j(a, b, r, e; p, s) * 6j(p, c, d, e; q', r)`

unconditionally for all weights `a b c d e p q' r s : ℕ` and all signs `ε δ ζ θ : ℤˣ`.

## Main definitions

* `TauCeti.UqSl2.quadrupleLeftInclusion`: normalized channel inclusion
  `L_e^(((εδ)ζ)θ) →ₗ[UqSl2 q] ((L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ) ⊗ L_d^θ` through intermediate weights
  `p` and `q'`.
* `TauCeti.UqSl2.quadrupleRightInclusion`: normalized channel inclusion
  `L_e^(ε(δ(ζθ))) →ₗ[UqSl2 q] L_a^ε ⊗ (L_b^δ ⊗ (L_c^ζ ⊗ L_d^θ))` through intermediate weights
  `r` and `s`.
* `TauCeti.UqSl2.quadrupleRightProjection`: normalized channel projection
  `L_a^ε ⊗ (L_b^δ ⊗ (L_c^ζ ⊗ L_d^θ)) →ₗ[UqSl2 q] L_e^(ε(δ(ζθ)))` onto intermediate weights `r`
  and `s`.

## Main results

* `TauCeti.UqSl2.quadrupleRightProjection_comp_inclusion`: orthogonality of right-comb quadruple
  channels.
* `TauCeti.UqSl2.biedenharn_elliott`: the quantum Biedenharn–Elliott pentagon identity for
  `sixJSymbol` summed over `t ∈ Finset.range (b + c + 1)`.
* `TauCeti.UqSl2.biedenharn_elliott_fin`: the equivalent sum over lowering-step indices
  `k : Fin (min b c + 1)` (`t = b + c - 2k`).
* `TauCeti.UqSl2.assoc_assoc_quadrupleLeftInclusion_vec`: explicit expansion of the two-step (and
  hence three-step) reassociation of any normalized `F`-ladder vector `v_k` (`k : ℤ`) of a
  left-comb channel into right-comb channels.

## References

* L. C. Biedenharn, *An identity satisfied by Racah coefficients*, Journal of Mathematics and
  Physics **31** (1953), 287–293.
* J. P. Elliott, *Theoretical studies in nuclear structure V*, Proceedings of the Royal Society of
  London A **218** (1953), 345–370.
* A. N. Kirillov and N. Yu. Reshetikhin, *Representations of the algebra `U_q(sl(2))`,
  `q`-orthogonal polynomials and invariants of links*, in *Infinite-Dimensional Lie Algebras and
  Groups*, World Scientific, 1989, pp. 285–339.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter XII.
* J. S. Carter, D. E. Flath, and M. Saito, *The Classical and Quantum 6j-symbols*, Mathematical
  Notes 43, Princeton University Press, 1995.
* P. Etingof, S. Gelaki, D. Nikshych, and V. Ostrik, *Tensor Categories*, Mathematical Surveys and
  Monographs 205, Sections 4.9 and 9.
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule

private theorem comp_sum {ι R M₁ M₂ M₃ : Type*} [Semiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (g : M₂ →ₗ[R] M₃) (s : Finset ι) (f : ι → M₁ →ₗ[R] M₂) :
    g.comp (∑ i ∈ s, f i) = ∑ i ∈ s, g.comp (f i) := by
  apply LinearMap.ext
  intro x
  simp [LinearMap.sum_apply]

variable {q : ℂ} [Fact (q ≠ 0)]

/-! ### Quadruple Clebsch–Gordan channel inclusions and projections -/

/-- Left-comb quadruple Clebsch–Gordan channel inclusion
`L_e^(((εδ)ζ)θ) →ₗ[UqSl2 q] ((L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ) ⊗ L_d^θ` through intermediate weights `p`
(in `L_a^ε ⊗ L_b^δ`) and `q'` (in `L_p^(εδ) ⊗ L_c^ζ`). -/
def quadrupleLeftInclusion (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d p q' e : ℕ) :
    LadderModule q e (((ε * δ) * ζ) * θ) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q)
        (Tensor ℂ (UqSl2 q)
          (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
          (LadderModule q c ζ))
        (LadderModule q d θ) :=
  (tensorMap ℂ (UqSl2 q)
      (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ p) LinearMap.id)
      LinearMap.id).comp <|
    (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq p (ε * δ) c ζ q') LinearMap.id).comp
      (clebschGordanWeightInclusion hq q' ((ε * δ) * ζ) d θ e)

/-- Intermediate pentagon vertex `(L_a^ε ⊗ (L_b^δ ⊗ L_c^ζ)) ⊗ L_d^θ` channel inclusion through
weights `t` (in `L_b^δ ⊗ L_c^ζ`) and `q'` (in `L_a^ε ⊗ L_t^(δζ)`). -/
private def vertexTwoInclusion (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d t q' e : ℕ) :
    LadderModule q e ((ε * (δ * ζ)) * θ) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q)
        (Tensor ℂ (UqSl2 q)
          (LadderModule q a ε)
          (Tensor ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)))
        (LadderModule q d θ) :=
  (tensorMap ℂ (UqSl2 q)
      (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ t))
      LinearMap.id).comp <|
    (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε t (δ * ζ) q') LinearMap.id).comp
      (clebschGordanWeightInclusion hq q' (ε * (δ * ζ)) d θ e)

/-- Intermediate pentagon vertex `L_a^ε ⊗ ((L_b^δ ⊗ L_c^ζ) ⊗ L_d^θ)` channel inclusion through
weights `t` (in `L_b^δ ⊗ L_c^ζ`) and `s` (in `L_t^(δζ) ⊗ L_d^θ`). -/
private def vertexThreeInclusion (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d t s e : ℕ) :
    LadderModule q e (ε * ((δ * ζ) * θ)) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q)
        (LadderModule q a ε)
        (Tensor ℂ (UqSl2 q)
          (Tensor ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ))
          (LadderModule q d θ)) :=
  (tensorMap ℂ (UqSl2 q) LinearMap.id
      (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq b δ c ζ t) LinearMap.id)).comp <|
    (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq t (δ * ζ) d θ s)).comp
      (clebschGordanWeightInclusion hq a ε s ((δ * ζ) * θ) e)

/-- Balanced pentagon vertex `(L_a^ε ⊗ L_b^δ) ⊗ (L_c^ζ ⊗ L_d^θ)` channel inclusion through
weights `p` (in `L_a^ε ⊗ L_b^δ`) and `r` (in `L_c^ζ ⊗ L_d^θ`). -/
private def vertexFiveInclusion (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d p r e : ℕ) :
    LadderModule q e ((ε * δ) * (ζ * θ)) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q)
        (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
        (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ)) :=
  (tensorMap ℂ (UqSl2 q)
      (clebschGordanWeightInclusion hq a ε b δ p)
      (clebschGordanWeightInclusion hq c ζ d θ r)).comp
    (clebschGordanWeightInclusion hq p (ε * δ) r (ζ * θ) e)

/-- Right-comb quadruple Clebsch–Gordan channel inclusion
`L_e^(ε(δ(ζθ))) →ₗ[UqSl2 q] L_a^ε ⊗ (L_b^δ ⊗ (L_c^ζ ⊗ L_d^θ))` through intermediate weights `r`
(in `L_c^ζ ⊗ L_d^θ`) and `s` (in `L_b^δ ⊗ L_r^(ζθ)`). -/
def quadrupleRightInclusion (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d r s e : ℕ) :
    LadderModule q e (ε * (δ * (ζ * θ))) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q)
        (LadderModule q a ε)
        (Tensor ℂ (UqSl2 q)
          (LadderModule q b δ)
          (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))) :=
  (tensorMap ℂ (UqSl2 q) LinearMap.id
      (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq c ζ d θ r))).comp <|
    (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ r (ζ * θ) s)).comp
      (clebschGordanWeightInclusion hq a ε s (δ * (ζ * θ)) e)

/-- Right-comb quadruple Clebsch–Gordan channel projection
`L_a^ε ⊗ (L_b^δ ⊗ (L_c^ζ ⊗ L_d^θ)) →ₗ[UqSl2 q] L_e^(ε(δ(ζθ)))` onto intermediate weights `r`
(in `L_c^ζ ⊗ L_d^θ`) and `s` (in `L_b^δ ⊗ L_r^(ζθ)`). -/
def quadrupleRightProjection (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d r s e : ℕ) :
    Tensor ℂ (UqSl2 q)
      (LadderModule q a ε)
      (Tensor ℂ (UqSl2 q)
        (LadderModule q b δ)
        (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))) →ₗ[UqSl2 q]
      LadderModule q e (ε * (δ * (ζ * θ))) :=
  (clebschGordanWeightProjection hq a ε s (δ * (ζ * θ)) e).comp <|
    (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightProjection hq b δ r (ζ * θ) s)).comp
      (tensorMap ℂ (UqSl2 q) LinearMap.id
        (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightProjection hq c ζ d θ r)))

/-- Orthogonality of right-comb quadruple Clebsch–Gordan channels. -/
theorem quadrupleRightProjection_comp_inclusion (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d r r' s s' e : ℕ) :
    (quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
      (quadrupleRightInclusion hq ε δ ζ θ a b c d r' s' e) =
      if r = r' ∧ s = s' ∧ IsClebschGordanTriple c d r ∧
          IsClebschGordanTriple b r s ∧ IsClebschGordanTriple a s e then
        LinearMap.id
      else 0 := by
  have hcomp : (quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
        (quadrupleRightInclusion hq ε δ ζ θ a b c d r' s' e) =
      (clebschGordanWeightProjection hq a ε s (δ * (ζ * θ)) e).comp
        ((tensorMap ℂ (UqSl2 q) LinearMap.id
          ((clebschGordanWeightProjection hq b δ r (ζ * θ) s).comp
            ((tensorMap ℂ (UqSl2 q) LinearMap.id
                ((clebschGordanWeightProjection hq c ζ d θ r).comp
                   (clebschGordanWeightInclusion hq c ζ d θ r'))).comp
              (clebschGordanWeightInclusion hq b δ r' (ζ * θ) s')))).comp
          (clebschGordanWeightInclusion hq a ε s' (δ * (ζ * θ)) e)) := by
    ext x
    simp [quadrupleRightProjection, quadrupleRightInclusion]
  rw [hcomp]
  by_cases h : r = r' ∧ s = s' ∧ IsClebschGordanTriple c d r ∧
      IsClebschGordanTriple b r s ∧ IsClebschGordanTriple a s e
  · obtain ⟨rfl, rfl, hcdr, hbrs, hase⟩ := h
    simp [hcdr, hbrs, hase,
      clebschGordanWeightProjection_comp_inclusion_self hq ζ θ hcdr,
      clebschGordanWeightProjection_comp_inclusion_self hq δ (ζ * θ) hbrs,
      clebschGordanWeightProjection_comp_inclusion_self hq ε (δ * (ζ * θ)) hase]
  · rw [ite_eq_right h]
    by_cases hrr : r = r'
    · subst hrr
      by_cases hcdr : IsClebschGordanTriple c d r
      · rw [clebschGordanWeightProjection_comp_inclusion_self hq ζ θ hcdr, tensorMap_id,
          LinearMap.id_comp]
        by_cases hss : s = s'
        · subst hss
          by_cases hbrs : IsClebschGordanTriple b r s
          · have hase : ¬ IsClebschGordanTriple a s e := fun hase =>
              h ⟨rfl, rfl, hcdr, hbrs, hase⟩
            simp [clebschGordanWeightInclusion_of_not_triple hq ε (δ * (ζ * θ)) hase]
          · simp [clebschGordanWeightInclusion_of_not_triple hq δ (ζ * θ) hbrs]
        · simp [clebschGordanWeightProjection_comp_inclusion_of_ne (a := b) (b := r)
            hq δ (ζ * θ) hss]
      · simp [clebschGordanWeightInclusion_of_not_triple hq ζ θ hcdr]
    · simp [clebschGordanWeightProjection_comp_inclusion_of_ne (a := c) (b := d) hq ζ θ hrr]

/-! ### Reassociation along the five edges of Mac Lane's pentagon -/

private theorem edge_one_two (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d p q' e : ℕ) :
    (tensorMap ℂ (UqSl2 q)
        (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
          (LadderModule q c ζ)).toLinearMap
        LinearMap.id).comp
      (quadrupleLeftInclusion hq ε δ ζ θ a b c d p q' e) =
      ∑ t ∈ Finset.range (b + c + 1),
        sixJSymbol hq ε δ ζ a b c q' p t •
          ((vertexTwoInclusion hq ε δ ζ θ a b c d t q' e).comp
            (LadderModule.congr rfl (congrArg (· * θ) (mul_assoc ε δ ζ))).toLinearMap) := by
  have hmerge : (tensorMap ℂ (UqSl2 q)
        (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
          (LadderModule q c ζ)).toLinearMap
        (LinearMap.id : LadderModule q d θ →ₗ[UqSl2 q] _)).comp
      (quadrupleLeftInclusion hq ε δ ζ θ a b c d p q' e) =
      (tensorMap ℂ (UqSl2 q)
        ((assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
            (LadderModule q c ζ)).toLinearMap.comp
          ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ p) LinearMap.id).comp
            (clebschGordanWeightInclusion hq p (ε * δ) c ζ q')))
        LinearMap.id).comp
      (clebschGordanWeightInclusion hq q' ((ε * δ) * ζ) d θ e) := by
    ext x
    simp [quadrupleLeftInclusion]
  rw [hmerge, assoc_comp_clebschGordanWeightInclusion hq ε δ ζ a b c q' p,
    tensorMap_sum_left,
    ← LinearMap.lcomp_apply' (S := ℕ) (clebschGordanWeightInclusion hq q' ((ε * δ) * ζ) d θ e),
    map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [LinearMap.lcomp_apply', tensorMap_smul_left, LinearMap.smul_comp]
  congr 1
  have hcongr := tensorMap_congr_comp_clebschGordanWeightInclusion hq
    (rfl : q' = q') (rfl : d = d) (mul_assoc ε δ ζ) (rfl : θ = θ) e
  simp only [congr_refl, LinearEquiv.refl_toLinearMap] at hcongr
  have hsplit : (tensorMap ℂ (UqSl2 q)
        ((tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ t)).comp
          ((clebschGordanWeightInclusion hq a ε t (δ * ζ) q').comp
            (LadderModule.congr rfl (mul_assoc ε δ ζ)).toLinearMap))
        LinearMap.id).comp
      (clebschGordanWeightInclusion hq q' ((ε * δ) * ζ) d θ e) =
      (tensorMap ℂ (UqSl2 q)
          (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ t))
          LinearMap.id).comp
        ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε t (δ * ζ) q')
            LinearMap.id).comp
          ((tensorMap ℂ (UqSl2 q)
              (LadderModule.congr rfl (mul_assoc ε δ ζ)).toLinearMap LinearMap.id).comp
            (clebschGordanWeightInclusion hq q' ((ε * δ) * ζ) d θ e))) := by
    ext x
    simp
  rw [hsplit, hcongr]
  rfl

private theorem edge_two_three (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d t q' e : ℕ) :
    (assoc ℂ (UqSl2 q) (LadderModule q a ε)
        (Tensor ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ))
        (LadderModule q d θ)).toLinearMap.comp
      (vertexTwoInclusion hq ε δ ζ θ a b c d t q' e) =
      ∑ s' ∈ Finset.range (t + d + 1),
        sixJSymbol hq ε (δ * ζ) θ a t d e q' s' •
          ((vertexThreeInclusion hq ε δ ζ θ a b c d t s' e).comp
            (LadderModule.congr rfl (mul_assoc ε (δ * ζ) θ)).toLinearMap) := by
  rw [vertexTwoInclusion, ← LinearMap.comp_assoc, ← tensorMap_tensorMap_comp_assoc_eq,
    LinearMap.comp_assoc, assoc_comp_clebschGordanWeightInclusion hq ε (δ * ζ) θ a t d e q',
    ← LinearMap.compRight_apply (S := ℕ)
      (tensorMap ℂ (UqSl2 q) LinearMap.id
        (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq b δ c ζ t) LinearMap.id)),
    map_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [LinearMap.compRight_apply, LinearMap.comp_smul]
  congr 1

private theorem edge_three_four (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d t s' e : ℕ) :
    (tensorMap ℂ (UqSl2 q) LinearMap.id
        (assoc ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)
          (LadderModule q d θ)).toLinearMap).comp
      (vertexThreeInclusion hq ε δ ζ θ a b c d t s' e) =
      ∑ r' ∈ Finset.range (c + d + 1),
        sixJSymbol hq δ ζ θ b c d s' t r' •
          ((quadrupleRightInclusion hq ε δ ζ θ a b c d r' s' e).comp
            (LadderModule.congr rfl (congrArg (ε * ·) (mul_assoc δ ζ θ))).toLinearMap) := by
  have hmerge : (tensorMap ℂ (UqSl2 q) (LinearMap.id : LadderModule q a ε →ₗ[UqSl2 q] _)
        (assoc ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)
          (LadderModule q d θ)).toLinearMap).comp
      (vertexThreeInclusion hq ε δ ζ θ a b c d t s' e) =
      (tensorMap ℂ (UqSl2 q) LinearMap.id
        ((assoc ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)
            (LadderModule q d θ)).toLinearMap.comp
          ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq b δ c ζ t) LinearMap.id).comp
            (clebschGordanWeightInclusion hq t (δ * ζ) d θ s')))).comp
      (clebschGordanWeightInclusion hq a ε s' ((δ * ζ) * θ) e) := by
    ext x
    simp [vertexThreeInclusion]
  rw [hmerge, assoc_comp_clebschGordanWeightInclusion hq δ ζ θ b c d s' t,
    tensorMap_sum_right,
    ← LinearMap.lcomp_apply' (S := ℕ) (clebschGordanWeightInclusion hq a ε s' ((δ * ζ) * θ) e),
    map_sum]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [LinearMap.lcomp_apply', tensorMap_smul_right, LinearMap.smul_comp]
  congr 1
  have hcongr := tensorMap_congr_comp_clebschGordanWeightInclusion hq
    (rfl : a = a) (rfl : s' = s') (rfl : ε = ε) (mul_assoc δ ζ θ) e
  simp only [congr_refl, LinearEquiv.refl_toLinearMap] at hcongr
  have hsplit : (tensorMap ℂ (UqSl2 q) LinearMap.id
        ((tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq c ζ d θ r')).comp
          ((clebschGordanWeightInclusion hq b δ r' (ζ * θ) s').comp
             (LadderModule.congr rfl (mul_assoc δ ζ θ)).toLinearMap))).comp
      (clebschGordanWeightInclusion hq a ε s' ((δ * ζ) * θ) e) =
      (tensorMap ℂ (UqSl2 q) LinearMap.id
          (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq c ζ d θ r'))).comp
        ((tensorMap ℂ (UqSl2 q) LinearMap.id
            (clebschGordanWeightInclusion hq b δ r' (ζ * θ) s')).comp
          ((tensorMap ℂ (UqSl2 q) LinearMap.id
              (LadderModule.congr rfl (mul_assoc δ ζ θ)).toLinearMap).comp
            (clebschGordanWeightInclusion hq a ε s' ((δ * ζ) * θ) e))) := by
    ext x
    simp
  rw [hsplit, hcongr]
  rfl

private theorem edge_one_five (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d p q' e : ℕ) :
    (assoc ℂ (UqSl2 q)
        (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
        (LadderModule q c ζ) (LadderModule q d θ)).toLinearMap.comp
      (quadrupleLeftInclusion hq ε δ ζ θ a b c d p q' e) =
      ∑ r' ∈ Finset.range (c + d + 1),
        sixJSymbol hq (ε * δ) ζ θ p c d e q' r' •
          ((vertexFiveInclusion hq ε δ ζ θ a b c d p r' e).comp
            (LadderModule.congr rfl (mul_assoc (ε * δ) ζ θ)).toLinearMap) := by
  rw [quadrupleLeftInclusion, ← LinearMap.comp_assoc, ← tensorMap_tensorMap_comp_assoc_eq,
    LinearMap.comp_assoc, assoc_comp_clebschGordanWeightInclusion hq (ε * δ) ζ θ p c d e q',
    ← LinearMap.compRight_apply (S := ℕ)
      (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ p)
        (tensorMap ℂ (UqSl2 q) LinearMap.id LinearMap.id)),
    map_sum]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [LinearMap.compRight_apply, LinearMap.comp_smul]
  congr 1
  simp only [vertexFiveInclusion, tensorMap_id, ← LinearMap.comp_assoc, ← tensorMap_comp,
    LinearMap.comp_id, LinearMap.id_comp]

private theorem edge_five_four (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d p r' e : ℕ) :
    (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))).toLinearMap.comp
      (vertexFiveInclusion hq ε δ ζ θ a b c d p r' e) =
      ∑ s' ∈ Finset.range (b + r' + 1),
        sixJSymbol hq ε δ (ζ * θ) a b r' e p s' •
          ((quadrupleRightInclusion hq ε δ ζ θ a b c d r' s' e).comp
            (LadderModule.congr rfl (mul_assoc ε δ (ζ * θ))).toLinearMap) := by
  have hfactor : vertexFiveInclusion hq ε δ ζ θ a b c d p r' e =
      (tensorMap ℂ (UqSl2 q) (tensorMap ℂ (UqSl2 q) LinearMap.id LinearMap.id)
          (clebschGordanWeightInclusion hq c ζ d θ r')).comp
        ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ p) LinearMap.id).comp
          (clebschGordanWeightInclusion hq p (ε * δ) r' (ζ * θ) e)) := by
    simp only [vertexFiveInclusion, tensorMap_id, ← LinearMap.comp_assoc, ← tensorMap_comp,
      LinearMap.comp_id, LinearMap.id_comp]
  rw [hfactor, ← LinearMap.comp_assoc, ← tensorMap_tensorMap_comp_assoc_eq,
    LinearMap.comp_assoc, assoc_comp_clebschGordanWeightInclusion hq ε δ (ζ * θ) a b r' e p,
    ← LinearMap.compRight_apply (S := ℕ)
      (tensorMap ℂ (UqSl2 q) LinearMap.id
        (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq c ζ d θ r'))),
    map_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [LinearMap.compRight_apply, LinearMap.comp_smul]
  congr 1

/-! ### Coordinate extraction and the Biedenharn–Elliott pentagon identity -/

private theorem homScalar_comp_congr (hq : IsGenericQuantumParameter q)
    {m₁ m₂ n : ℕ} {η₁ η₂ η₃ : ℤˣ} (hm : m₁ = m₂) (hη : η₁ = η₂)
    (f : LadderModule q m₂ η₂ →ₗ[UqSl2 q] LadderModule q n η₃) :
    homScalar (f.comp (LadderModule.congr hm hη).toLinearMap) = homScalar f := by
  rw [homScalar_comp hq, homScalar_congr, mul_one]

private theorem homScalar_quadrupleRight_sum (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d e r r' s : ℕ) (α : ℕ → ℂ) (n : ℕ) :
    (∑ s' ∈ Finset.range n,
        α s' * homScalar ((quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
          (quadrupleRightInclusion hq ε δ ζ θ a b c d r' s' e))) =
      if s < n ∧ r = r' ∧ IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
          IsClebschGordanTriple a s e then
        α s
      else 0 := by
  by_cases h : s < n ∧ r = r' ∧ IsClebschGordanTriple c d r ∧
      IsClebschGordanTriple b r s ∧ IsClebschGordanTriple a s e
  · obtain ⟨hsn, rfl, hcdr, hbrs, hase⟩ := h
    rw [ite_eq_left ⟨hsn, rfl, hcdr, hbrs, hase⟩, Finset.sum_eq_single s]
    · simp [quadrupleRightProjection_comp_inclusion, hcdr, hbrs, hase]
    · intro s' _ hne
      simp [quadrupleRightProjection_comp_inclusion, Ne.symm hne]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hsn)).elim
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun s' hs' => ?_
    rw [quadrupleRightProjection_comp_inclusion]
    split_ifs with hc
    · obtain ⟨rfl, rfl, hcdr, hbrs, hase⟩ := hc
      exact (h ⟨Finset.mem_range.mp hs', rfl, hcdr, hbrs, hase⟩).elim
    · simp

private theorem homScalar_two_step (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d e p q' r s : ℕ) :
    homScalar ((quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
      ((assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
          (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))).toLinearMap.comp
        ((assoc ℂ (UqSl2 q)
            (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
            (LadderModule q c ζ) (LadderModule q d θ)).toLinearMap.comp
          (quadrupleLeftInclusion hq ε δ ζ θ a b c d p q' e)))) =
      if IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
          IsClebschGordanTriple a s e then
        sixJSymbol hq ε δ (ζ * θ) a b r e p s *
          sixJSymbol hq (ε * δ) ζ θ p c d e q' r
      else 0 := by
  set P := quadrupleRightProjection hq ε δ ζ θ a b c d r s e
  set A₅₄ := (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
    (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))).toLinearMap
  rw [← LinearMap.comp_assoc, edge_one_five]
  simp only [comp_sum, LinearMap.comp_smul, map_sum, map_smul, smul_eq_mul,
    ← LinearMap.comp_assoc, homScalar_comp_congr hq]
  have hterm : ∀ r' ∈ Finset.range (c + d + 1),
      sixJSymbol hq (ε * δ) ζ θ p c d e q' r' *
          homScalar ((P.comp A₅₄).comp (vertexFiveInclusion hq ε δ ζ θ a b c d p r' e)) =
        if r = r' ∧ IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
            IsClebschGordanTriple a s e then
          sixJSymbol hq ε δ (ζ * θ) a b r e p s *
            sixJSymbol hq (ε * δ) ζ θ p c d e q' r
        else 0 := by
    intro r' _
    rw [LinearMap.comp_assoc, edge_five_four]
    simp only [comp_sum, LinearMap.comp_smul, map_sum, map_smul, smul_eq_mul,
      ← LinearMap.comp_assoc, homScalar_comp_congr hq]
    rw [homScalar_quadrupleRight_sum]
    by_cases h₂ : r = r' ∧ IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
        IsClebschGordanTriple a s e
    · obtain ⟨rfl, hcdr, hbrs, hase⟩ := h₂
      have h₁ : s < b + r + 1 ∧ r = r ∧ IsClebschGordanTriple c d r ∧
          IsClebschGordanTriple b r s ∧ IsClebschGordanTriple a s e :=
        ⟨Nat.lt_succ_of_le hbrs.le_add, rfl, hcdr, hbrs, hase⟩
      rw [ite_eq_left h₁, ite_eq_left ⟨rfl, hcdr, hbrs, hase⟩]
      ring
    · rw [ite_eq_right h₂, ite_eq_right fun h₁ => h₂ h₁.2, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases htri : IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
      IsClebschGordanTriple a s e
  · rw [ite_eq_left htri, Finset.sum_eq_single r]
    · simp [htri]
    · intro r' _ hne
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le htri.1.le_add))).elim
  · rw [ite_eq_right htri]
    exact Finset.sum_eq_zero fun r' _ => ite_eq_right fun hr => htri hr.2

private theorem homScalar_vertexThree (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d e t r s s' : ℕ) :
    homScalar ((quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
      ((tensorMap ℂ (UqSl2 q) LinearMap.id
          (assoc ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)
            (LadderModule q d θ)).toLinearMap).comp
        (vertexThreeInclusion hq ε δ ζ θ a b c d t s' e))) =
      if s = s' ∧ IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
          IsClebschGordanTriple a s e then
        sixJSymbol hq δ ζ θ b c d s t r
      else 0 := by
  rw [edge_three_four]
  simp only [comp_sum, LinearMap.comp_smul, map_sum, map_smul, smul_eq_mul,
    ← LinearMap.comp_assoc, homScalar_comp_congr hq]
  by_cases hs : s = s' ∧ IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
      IsClebschGordanTriple a s e
  · obtain ⟨rfl, hcdr, hbrs, hase⟩ := hs
    rw [ite_eq_left ⟨rfl, hcdr, hbrs, hase⟩, Finset.sum_eq_single r]
    · simp [quadrupleRightProjection_comp_inclusion, hcdr, hbrs, hase]
    · intro r' _ hne
      simp [quadrupleRightProjection_comp_inclusion, Ne.symm hne]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hcdr.le_add))).elim
  · rw [ite_eq_right hs]
    refine Finset.sum_eq_zero fun r' _ => ?_
    rw [quadrupleRightProjection_comp_inclusion]
    split_ifs with hc
    · exact (hs ⟨hc.2.1, hc.2.2⟩).elim
    · simp

private theorem homScalar_vertexTwo (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d e t q' r s : ℕ) :
    homScalar ((quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
      ((tensorMap ℂ (UqSl2 q) LinearMap.id
          (assoc ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)
            (LadderModule q d θ)).toLinearMap).comp
        ((assoc ℂ (UqSl2 q) (LadderModule q a ε)
            (Tensor ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ))
            (LadderModule q d θ)).toLinearMap.comp
          (vertexTwoInclusion hq ε δ ζ θ a b c d t q' e)))) =
      if IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
          IsClebschGordanTriple a s e then
        sixJSymbol hq δ ζ θ b c d s t r *
          sixJSymbol hq ε (δ * ζ) θ a t d e q' s
      else 0 := by
  set P := quadrupleRightProjection hq ε δ ζ θ a b c d r s e
  set A₃₄ := tensorMap ℂ (UqSl2 q) (LinearMap.id : LadderModule q a ε →ₗ[UqSl2 q] _)
    (assoc ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)
      (LadderModule q d θ)).toLinearMap
  rw [← LinearMap.comp_assoc, edge_two_three]
  simp only [comp_sum, LinearMap.comp_smul, map_sum, map_smul, smul_eq_mul,
    ← LinearMap.comp_assoc, homScalar_comp_congr hq]
  have hmid : ∀ s' ∈ Finset.range (t + d + 1),
      sixJSymbol hq ε (δ * ζ) θ a t d e q' s' *
          homScalar ((P.comp A₃₄).comp (vertexThreeInclusion hq ε δ ζ θ a b c d t s' e)) =
        if s = s' ∧ IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
            IsClebschGordanTriple a s e then
          sixJSymbol hq δ ζ θ b c d s t r *
            sixJSymbol hq ε (δ * ζ) θ a t d e q' s
        else 0 := by
    intro s' _
    rw [LinearMap.comp_assoc, homScalar_vertexThree]
    split_ifs with hs
    · obtain ⟨rfl, _⟩ := hs
      ring
    · exact mul_zero _
  rw [Finset.sum_congr rfl hmid]
  by_cases htri : IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
      IsClebschGordanTriple a s e
  · rw [ite_eq_left htri]
    by_cases hs_mem : s ∈ Finset.range (t + d + 1)
    · rw [Finset.sum_eq_single s]
      · simp [htri]
      · intro s' _ hne
        simp [Ne.symm hne]
      · intro hnot
        exact (hnot hs_mem).elim
    · have hnot_tds : ¬ IsClebschGordanTriple t d s := fun htr =>
        hs_mem (Finset.mem_range.mpr (Nat.lt_succ_of_le htr.le_add))
      rw [sixJSymbol_eq_zero_of_not_triple hq δ ζ θ (fun h => hnot_tds h.2.1), zero_mul]
      refine Finset.sum_eq_zero fun s' hs' => ?_
      rw [ite_eq_right]
      rintro ⟨rfl, _⟩
      exact hs_mem hs'
  · rw [ite_eq_right htri, Finset.sum_eq_zero fun s' _ => ite_eq_right fun hs => htri hs.2]

private theorem homScalar_three_step (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d e p q' r s : ℕ) :
    homScalar ((quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
      ((tensorMap ℂ (UqSl2 q) LinearMap.id
          (assoc ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)
            (LadderModule q d θ)).toLinearMap).comp
        ((assoc ℂ (UqSl2 q) (LadderModule q a ε)
            (Tensor ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ))
            (LadderModule q d θ)).toLinearMap.comp
          ((tensorMap ℂ (UqSl2 q)
              (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
                (LadderModule q c ζ)).toLinearMap
              LinearMap.id).comp
            (quadrupleLeftInclusion hq ε δ ζ θ a b c d p q' e))))) =
      if IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
          IsClebschGordanTriple a s e then
        ∑ t ∈ Finset.range (b + c + 1),
          sixJSymbol hq δ ζ θ b c d s t r *
            sixJSymbol hq ε (δ * ζ) θ a t d e q' s *
            sixJSymbol hq ε δ ζ a b c q' p t
      else 0 := by
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, edge_one_two]
  simp only [comp_sum, LinearMap.comp_smul, map_sum, map_smul, smul_eq_mul,
    ← LinearMap.comp_assoc, homScalar_comp_congr hq]
  have hterm : ∀ t ∈ Finset.range (b + c + 1),
      sixJSymbol hq ε δ ζ a b c q' p t *
          homScalar ((((quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
            (tensorMap ℂ (UqSl2 q) LinearMap.id
              (assoc ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)
                (LadderModule q d θ)).toLinearMap)).comp
            (assoc ℂ (UqSl2 q) (LadderModule q a ε)
              (Tensor ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ))
              (LadderModule q d θ)).toLinearMap).comp
            (vertexTwoInclusion hq ε δ ζ θ a b c d t q' e)) =
        if IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
            IsClebschGordanTriple a s e then
          sixJSymbol hq δ ζ θ b c d s t r *
            sixJSymbol hq ε (δ * ζ) θ a t d e q' s *
            sixJSymbol hq ε δ ζ a b c q' p t
        else 0 := by
    intro t _
    simp only [LinearMap.comp_assoc]
    rw [homScalar_vertexTwo]
    split_ifs
    · ring
    · exact mul_zero _
  rw [Finset.sum_congr rfl hterm]
  split_ifs
  · rfl
  · simp

/-- **The quantum Biedenharn–Elliott pentagon identity** for the `U_q(sl₂)` `6j` symbols on
`L_a^ε ⊗ L_b^δ ⊗ L_c^ζ ⊗ L_d^θ` under the actual coproduct tensor associator, in the normalized
`α₀ = 1` / `F`-ladder Clebsch–Gordan convention. -/
theorem biedenharn_elliott (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d e p q' r s : ℕ) :
    ∑ t ∈ Finset.range (b + c + 1),
        sixJSymbol hq δ ζ θ b c d s t r *
          sixJSymbol hq ε (δ * ζ) θ a t d e q' s *
          sixJSymbol hq ε δ ζ a b c q' p t =
      sixJSymbol hq ε δ (ζ * θ) a b r e p s *
        sixJSymbol hq (ε * δ) ζ θ p c d e q' r := by
  by_cases htri : IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
      IsClebschGordanTriple a s e
  · have hpent := congrArg LinearEquiv.toLinearMap
      (assoc_pentagon ℂ (UqSl2 q)
        (LadderModule q a ε) (LadderModule q b δ)
        (LadderModule q c ζ) (LadderModule q d θ))
    have heq := congrArg
      (fun Φ => homScalar ((quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
        (Φ.comp (quadrupleLeftInclusion hq ε δ ζ θ a b c d p q' e))))
      hpent
    simp only [LinearEquiv.coe_trans, toLinearMap_tensorCongr, LinearEquiv.refl_toLinearMap,
      LinearMap.comp_assoc] at heq
    rw [homScalar_two_step, homScalar_three_step, ite_eq_left htri, ite_eq_left htri] at heq
    exact heq.symm
  · have hrhs : sixJSymbol hq ε δ (ζ * θ) a b r e p s *
        sixJSymbol hq (ε * δ) ζ θ p c d e q' r = 0 := by
      by_cases hcdr : IsClebschGordanTriple c d r
      · by_cases hbrs : IsClebschGordanTriple b r s
        · have hase : ¬ IsClebschGordanTriple a s e := fun hase => htri ⟨hcdr, hbrs, hase⟩
          rw [sixJSymbol_eq_zero_of_not_triple hq ε δ (ζ * θ) (fun h => hase h.2.2.2), zero_mul]
        · rw [sixJSymbol_eq_zero_of_not_triple hq ε δ (ζ * θ) (fun h => hbrs h.2.2.1), zero_mul]
      · rw [sixJSymbol_eq_zero_of_not_triple hq (ε * δ) ζ θ (fun h => hcdr h.2.2.1), mul_zero]
    rw [hrhs]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases hcdr : IsClebschGordanTriple c d r
    · by_cases hbrs : IsClebschGordanTriple b r s
      · have hase : ¬ IsClebschGordanTriple a s e := fun hase => htri ⟨hcdr, hbrs, hase⟩
        rw [sixJSymbol_eq_zero_of_not_triple hq ε (δ * ζ) θ (fun h => hase h.2.2.2),
          mul_zero, zero_mul]
      · rw [sixJSymbol_eq_zero_of_not_triple hq δ ζ θ (fun h => hbrs h.2.2.2),
          zero_mul, zero_mul]
    · rw [sixJSymbol_eq_zero_of_not_triple hq δ ζ θ (fun h => hcdr h.2.2.1),
        zero_mul, zero_mul]

/-- Lowering-step form of the quantum Biedenharn–Elliott pentagon identity, summed over
`k : Fin (min b c + 1)` with intermediate weight `t = b + c - 2k`. -/
theorem biedenharn_elliott_fin (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d e p q' r s : ℕ) :
    ∑ k : Fin (min b c + 1),
        sixJSymbol hq δ ζ θ b c d s (b + c - 2 * (k : ℕ)) r *
          sixJSymbol hq ε (δ * ζ) θ a (b + c - 2 * (k : ℕ)) d e q' s *
          sixJSymbol hq ε δ ζ a b c q' p (b + c - 2 * (k : ℕ)) =
      sixJSymbol hq ε δ (ζ * θ) a b r e p s *
        sixJSymbol hq (ε * δ) ζ θ p c d e q' r := by
  rw [← biedenharn_elliott hq ε δ ζ θ a b c d e p q' r s,
    sum_range_of_not_isClebschGordanTriple b c _ fun t htr => by
      rw [sixJSymbol_eq_zero_of_not_triple hq δ ζ θ (fun h => htr h.1), zero_mul, zero_mul]]

/-- Explicit expansion of the quadruple associator `assoc A B (C ⊗ D) ∘ assoc (A ⊗ B) C D` (and
equivalently `(id_A ⊗ assoc B C D) ∘ assoc A (B ⊗ C) D ∘ (assoc A B C ⊗ id_D)` by
`BialgebraModule.assoc_assoc`) on any normalized `F`-ladder vector `v_k` (`k : ℤ`, including
`k = 0` for the `α₀ = 1` highest vector) of a left-comb quadruple Clebsch–Gordan channel. -/
theorem assoc_assoc_quadrupleLeftInclusion_vec (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d p q' e : ℕ) (k : ℤ) :
    assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))
        (assoc ℂ (UqSl2 q)
          (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
          (LadderModule q c ζ) (LadderModule q d θ)
          (quadrupleLeftInclusion hq ε δ ζ θ a b c d p q' e
            (vec q e (((ε * δ) * ζ) * θ) k))) =
      ∑ r ∈ Finset.range (c + d + 1), ∑ s ∈ Finset.range (b + r + 1),
        (sixJSymbol hq (ε * δ) ζ θ p c d e q' r *
            sixJSymbol hq ε δ (ζ * θ) a b r e p s) •
          quadrupleRightInclusion hq ε δ ζ θ a b c d r s e
            (vec q e (ε * (δ * (ζ * θ))) k) := by
  have h₁ := congrArg (fun f =>
      assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))
        (f (vec q e (((ε * δ) * ζ) * θ) k)))
    (edge_one_five hq ε δ ζ θ a b c d p q' e)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.sum_apply, LinearMap.smul_apply,
    congr_vec, map_sum] at h₁
  rw [h₁]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h₂ := congrArg (fun f => f (vec q e ((ε * δ) * (ζ * θ)) k))
    (edge_five_four hq ε δ ζ θ a b c d p r e)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.sum_apply, LinearMap.smul_apply,
    congr_vec] at h₂
  rw [LinearMapClass.map_smul_of_tower, h₂, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_smul]

end TauCeti.UqSl2

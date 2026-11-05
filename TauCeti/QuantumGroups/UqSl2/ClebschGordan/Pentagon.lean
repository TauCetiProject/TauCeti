/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.SixJ

/-!
# The quantum Biedenharn–Elliott pentagon identity

On a quadruple tensor product `L_a^ε ⊗ L_b^δ ⊗ L_c^ζ ⊗ L_d^θ` of signed `U_q(sl₂)` ladder modules,
Mac Lane's pentagon identity (`BialgebraModule.assoc_pentagon`) equates the two-step and three-step
reassociation paths from `((L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ) ⊗ L_d^θ` to
`L_a^ε ⊗ (L_b^δ ⊗ (L_c^ζ ⊗ L_d^θ))`. Expanding both paths in normalized Clebsch–Gordan channels and
extracting Schur scalars yields the quantum **Biedenharn–Elliott pentagon identity**
(`biedenharn_elliott`) unconditionally for all weights and signs.

## Main definitions

* `TauCeti.UqSl2.quadrupleLeftInclusion`: left-comb channel inclusion into
  `((L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ) ⊗ L_d^θ`.
* `TauCeti.UqSl2.quadrupleRightInclusion`, `TauCeti.UqSl2.quadrupleRightProjection`: right-comb
  channel inclusion and projection on `L_a^ε ⊗ (L_b^δ ⊗ (L_c^ζ ⊗ L_d^θ))`.

## Main results

* `TauCeti.UqSl2.quadrupleRightProjection_comp_inclusion`: orthogonality of right-comb channels.
* `TauCeti.UqSl2.biedenharn_elliott`, `TauCeti.UqSl2.biedenharn_elliott_fin`: the quantum
  Biedenharn–Elliott pentagon identity in weight and lowering-step coordinates.
* `TauCeti.UqSl2.assoc_assoc_quadrupleLeftInclusion_vec`: explicit quadruple associator expansion
  on normalized `F`-ladder vectors `v_k` (`k : ℤ`).

## References

* L. C. Biedenharn, *An identity satisfied by Racah coefficients*, J. Math. Phys. **31** (1953),
  287–293.
* J. P. Elliott, *Theoretical studies in nuclear structure V*, Proc. R. Soc. Lond. A **218**
  (1953), 345–370.
* A. N. Kirillov and N. Yu. Reshetikhin, *Representations of the algebra `U_q(sl(2))`,
  `q`-orthogonal polynomials and invariants of links*, World Scientific, 1989, pp. 285–339.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter XII.
* P. Etingof, S. Gelaki, D. Nikshych, and V. Ostrik, *Tensor Categories*, Sections 4.9 and 9.
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule

variable {q : ℂ} [Fact (q ≠ 0)]

/-- Left-comb quadruple Clebsch–Gordan channel inclusion
`L_e^(((εδ)ζ)θ) →ₗ[UqSl2 q] ((L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ) ⊗ L_d^θ` via intermediate weights `p, q'`. -/
def quadrupleLeftInclusion (hq : IsGenericQuantumParameter q) (ε δ ζ θ : ℤˣ) (a b c d p q' e : ℕ) :
    LadderModule q e (((ε * δ) * ζ) * θ) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q)
        (Tensor ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
          (LadderModule q c ζ)) (LadderModule q d θ) :=
  (tensorMap ℂ (UqSl2 q)
      (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ p) LinearMap.id)
      LinearMap.id).comp <|
    (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq p (ε * δ) c ζ q') LinearMap.id).comp
      (clebschGordanWeightInclusion hq q' ((ε * δ) * ζ) d θ e)

private def vertexTwoInclusion (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d t q' e : ℕ) :
    LadderModule q e ((ε * (δ * ζ)) * θ) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q)
        (Tensor ℂ (UqSl2 q) (LadderModule q a ε)
          (Tensor ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ))) (LadderModule q d θ) :=
  (tensorMap ℂ (UqSl2 q)
      (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ t))
      LinearMap.id).comp <|
    (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε t (δ * ζ) q') LinearMap.id).comp
      (clebschGordanWeightInclusion hq q' (ε * (δ * ζ)) d θ e)

private def vertexThreeInclusion (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d t s e : ℕ) :
    LadderModule q e (ε * ((δ * ζ) * θ)) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q) (LadderModule q a ε)
        (Tensor ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ))
          (LadderModule q d θ)) :=
  (tensorMap ℂ (UqSl2 q) LinearMap.id
      (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq b δ c ζ t) LinearMap.id)).comp <|
    (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq t (δ * ζ) d θ s)).comp
      (clebschGordanWeightInclusion hq a ε s ((δ * ζ) * θ) e)

private def vertexFiveInclusion (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d p r e : ℕ) :
    LadderModule q e ((ε * δ) * (ζ * θ)) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
        (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ)) :=
  (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ p)
      (clebschGordanWeightInclusion hq c ζ d θ r)).comp
    (clebschGordanWeightInclusion hq p (ε * δ) r (ζ * θ) e)

/-- Right-comb quadruple Clebsch–Gordan channel inclusion
`L_e^(ε(δ(ζθ))) →ₗ[UqSl2 q] L_a^ε ⊗ (L_b^δ ⊗ (L_c^ζ ⊗ L_d^θ))` via intermediate weights `r, s`. -/
def quadrupleRightInclusion (hq : IsGenericQuantumParameter q) (ε δ ζ θ : ℤˣ) (a b c d r s e : ℕ) :
    LadderModule q e (ε * (δ * (ζ * θ))) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q) (LadderModule q a ε)
        (Tensor ℂ (UqSl2 q) (LadderModule q b δ)
          (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))) :=
  (tensorMap ℂ (UqSl2 q) LinearMap.id
      (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq c ζ d θ r))).comp <|
    (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ r (ζ * θ) s)).comp
      (clebschGordanWeightInclusion hq a ε s (δ * (ζ * θ)) e)

/-- Right-comb quadruple Clebsch–Gordan channel projection
`L_a^ε ⊗ (L_b^δ ⊗ (L_c^ζ ⊗ L_d^θ)) →ₗ[UqSl2 q] L_e^(ε(δ(ζθ)))` onto intermediate weights `r, s`. -/
def quadrupleRightProjection (hq : IsGenericQuantumParameter q) (ε δ ζ θ : ℤˣ) (a b c d r s e : ℕ) :
    Tensor ℂ (UqSl2 q) (LadderModule q a ε)
      (Tensor ℂ (UqSl2 q) (LadderModule q b δ)
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
    ext x; simp [quadrupleRightProjection, quadrupleRightInclusion]
  rw [hcomp]
  by_cases h : r = r' ∧ s = s' ∧ IsClebschGordanTriple c d r ∧
      IsClebschGordanTriple b r s ∧ IsClebschGordanTriple a s e
  · rcases h with ⟨rfl, rfl, hcdr, hbrs, hase⟩
    simp [hcdr, hbrs, hase,
      clebschGordanWeightProjection_comp_inclusion_self hq ζ θ hcdr,
      clebschGordanWeightProjection_comp_inclusion_self hq δ (ζ * θ) hbrs,
      clebschGordanWeightProjection_comp_inclusion_self hq ε (δ * (ζ * θ)) hase]
  · simp only [h, ↓reduceIte]
    by_cases hrr : r = r'
    · subst hrr
      by_cases hcdr : IsClebschGordanTriple c d r
      · rw [clebschGordanWeightProjection_comp_inclusion_self hq ζ θ hcdr, tensorMap_id,
          LinearMap.id_comp]
        by_cases hss : s = s'
        · subst hss
          by_cases hbrs : IsClebschGordanTriple b r s
          · simp [clebschGordanWeightInclusion_eq_zero_of_not_isClebschGordanTriple hq
              ε (δ * (ζ * θ)) fun hase => h ⟨rfl, rfl, hcdr, hbrs, hase⟩]
          · simp [clebschGordanWeightInclusion_eq_zero_of_not_isClebschGordanTriple hq
              δ (ζ * θ) hbrs]
        · simp [clebschGordanWeightProjection_comp_inclusion_of_ne (a := b) (b := r)
            hq δ (ζ * θ) hss]
      · simp [clebschGordanWeightInclusion_eq_zero_of_not_isClebschGordanTriple hq ζ θ hcdr]
    · simp [clebschGordanWeightProjection_comp_inclusion_of_ne (a := c) (b := d) hq ζ θ hrr]

/-! ### Reassociation along the five edges of Mac Lane's pentagon -/

private theorem edge_one_two (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d p q' e : ℕ) :
    (tensorMap ℂ (UqSl2 q)
        (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
          (LadderModule q c ζ)).toLinearMap LinearMap.id).comp
      (quadrupleLeftInclusion hq ε δ ζ θ a b c d p q' e) =
      ∑ t ∈ Finset.range (b + c + 1),
        sixJSymbol hq ε δ ζ a b c q' p t •
          ((vertexTwoInclusion hq ε δ ζ θ a b c d t q' e).comp
            (LadderModule.congr rfl (congrArg (· * θ) (mul_assoc ε δ ζ))).toLinearMap) := by
  rw [quadrupleLeftInclusion, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
    ← tensorMap_comp_left, ← tensorMap_comp_left,
    LinearMap.comp_assoc (clebschGordanWeightInclusion hq p (ε * δ) c ζ q'),
    assoc_comp_clebschGordanWeightInclusion hq ε δ ζ a b c q' p, tensorMap_sum_left,
    LinearMap.finsetSum_comp]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [tensorMap_smul_left, LinearMap.smul_comp]
  congr 1
  have hcongr := tensorMap_congr_comp_clebschGordanWeightInclusion hq
    (rfl : q' = q') (rfl : d = d) (mul_assoc ε δ ζ) (rfl : θ = θ) e
  simp only [congr_refl, LinearEquiv.refl_toLinearMap] at hcongr
  simp only [vertexTwoInclusion, tensorMap_comp_left, LinearMap.comp_assoc, hcongr]

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
    LinearMap.comp_finsetSum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [LinearMap.comp_smul]
  simp only [vertexThreeInclusion, LinearMap.comp_assoc]

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
  rw [vertexThreeInclusion, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
    ← tensorMap_comp_right, ← tensorMap_comp_right,
    LinearMap.comp_assoc (clebschGordanWeightInclusion hq t (δ * ζ) d θ s'),
    assoc_comp_clebschGordanWeightInclusion hq δ ζ θ b c d s' t, tensorMap_sum_right,
    LinearMap.finsetSum_comp]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [tensorMap_smul_right, LinearMap.smul_comp]
  congr 1
  have hcongr := tensorMap_congr_comp_clebschGordanWeightInclusion hq
    (rfl : a = a) (rfl : s' = s') (rfl : ε = ε) (mul_assoc δ ζ θ) e
  simp only [congr_refl, LinearEquiv.refl_toLinearMap] at hcongr
  simp only [quadrupleRightInclusion, tensorMap_comp_right, LinearMap.comp_assoc, hcongr]

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
    LinearMap.comp_finsetSum]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [LinearMap.comp_smul]
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
    LinearMap.comp_finsetSum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [LinearMap.comp_smul]
  simp only [quadrupleRightInclusion, LinearMap.comp_assoc]

/-! ### Coordinate extraction and the Biedenharn–Elliott pentagon identity -/

private theorem homScalar_quadrupleRight_of_triples (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) {a b c d r s e : ℕ}
    (htri : IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
      IsClebschGordanTriple a s e) (r' s' : ℕ) :
    homScalar ((quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
      (quadrupleRightInclusion hq ε δ ζ θ a b c d r' s' e)) =
      if r = r' ∧ s = s' then 1 else 0 := by
  rw [quadrupleRightProjection_comp_inclusion]
  by_cases h : r = r' ∧ s = s'
  · rcases h with ⟨rfl, rfl⟩; simp [htri.1, htri.2.1, htri.2.2]
  · simp [h, show ¬ (r = r' ∧ s = s' ∧ IsClebschGordanTriple c d r ∧
      IsClebschGordanTriple b r s ∧ IsClebschGordanTriple a s e) by tauto]

private theorem homScalar_comp_sum_smul_comp_congr {ι M : Type*} [AddCommMonoid M]
    [Module ℂ M] [Module (UqSl2 q) M] [IsScalarTower ℂ (UqSl2 q) M]
    (hq : IsGenericQuantumParameter q) {e : ℕ} {η₁ η₂ η₃ : ℤˣ} (hη : η₁ = η₂)
    (P : M →ₗ[UqSl2 q] LadderModule q e η₃) (s : Finset ι) (c : ι → ℂ)
    (X : ι → LadderModule q e η₂ →ₗ[UqSl2 q] M) :
    homScalar (P.comp (∑ i ∈ s, c i • ((X i).comp (LadderModule.congr rfl hη).toLinearMap))) =
      ∑ i ∈ s, c i * homScalar (P.comp (X i)) := by
  simp only [LinearMap.comp_finsetSum, LinearMap.comp_smul, map_sum, map_smul, smul_eq_mul,
    ← LinearMap.comp_assoc, homScalar_comp hq, homScalar_congr, mul_one]

private theorem homScalar_two_step (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) {a b c d e p q' r s : ℕ}
    (htri : IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
      IsClebschGordanTriple a s e) :
    homScalar ((quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
      ((assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
          (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))).toLinearMap.comp
        ((assoc ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
            (LadderModule q c ζ) (LadderModule q d θ)).toLinearMap.comp
          (quadrupleLeftInclusion hq ε δ ζ θ a b c d p q' e)))) =
      sixJSymbol hq ε δ (ζ * θ) a b r e p s * sixJSymbol hq (ε * δ) ζ θ p c d e q' r := by
  rw [← LinearMap.comp_assoc, edge_one_five, homScalar_comp_sum_smul_comp_congr hq]
  rw [Finset.sum_eq_single r]
  · rw [LinearMap.comp_assoc, edge_five_four, homScalar_comp_sum_smul_comp_congr hq]
    simp only [homScalar_quadrupleRight_of_triples hq ε δ ζ θ htri]
    rw [Finset.sum_eq_single s]
    · simp [mul_comm]
    · intro s' _ hne; simp [Ne.symm hne]
    · exact fun h => (h htri.2.1.mem_range).elim
  · intro r' _ hne
    rw [LinearMap.comp_assoc, edge_five_four, homScalar_comp_sum_smul_comp_congr hq]
    simp [homScalar_quadrupleRight_of_triples hq ε δ ζ θ htri, Ne.symm hne]
  · exact fun h => (h htri.1.mem_range).elim

private theorem homScalar_three_step (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) {a b c d e p q' r s : ℕ}
    (htri : IsClebschGordanTriple c d r ∧ IsClebschGordanTriple b r s ∧
      IsClebschGordanTriple a s e) :
    homScalar ((quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
      ((tensorMap ℂ (UqSl2 q) LinearMap.id
          (assoc ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)
            (LadderModule q d θ)).toLinearMap).comp
        ((assoc ℂ (UqSl2 q) (LadderModule q a ε)
            (Tensor ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ))
            (LadderModule q d θ)).toLinearMap.comp
          ((tensorMap ℂ (UqSl2 q)
              (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
                (LadderModule q c ζ)).toLinearMap LinearMap.id).comp
            (quadrupleLeftInclusion hq ε δ ζ θ a b c d p q' e))))) =
      ∑ t ∈ Finset.range (b + c + 1),
        sixJSymbol hq δ ζ θ b c d s t r *
          sixJSymbol hq ε (δ * ζ) θ a t d e q' s *
          sixJSymbol hq ε δ ζ a b c q' p t := by
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, edge_one_two,
    homScalar_comp_sum_smul_comp_congr hq]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [LinearMap.comp_assoc, edge_two_three, homScalar_comp_sum_smul_comp_congr hq]
  have hinner : ∀ s' ∈ Finset.range (t + d + 1),
      sixJSymbol hq ε (δ * ζ) θ a t d e q' s' *
        homScalar (((quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
          (tensorMap ℂ (UqSl2 q) LinearMap.id
            (assoc ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)
              (LadderModule q d θ)).toLinearMap)).comp
          (vertexThreeInclusion hq ε δ ζ θ a b c d t s' e)) =
      if s = s' then sixJSymbol hq ε (δ * ζ) θ a t d e q' s * sixJSymbol hq δ ζ θ b c d s t r
      else 0 := by
    intro s' _
    rw [LinearMap.comp_assoc, edge_three_four, homScalar_comp_sum_smul_comp_congr hq]
    simp only [homScalar_quadrupleRight_of_triples hq ε δ ζ θ htri]
    rw [Finset.sum_eq_single r]
    · rcases eq_or_ne s s' with rfl | hs; · simp
      · simp [hs]
    · intro r' _ hne; simp [Ne.symm hne]
    · exact fun h => (h htri.1.mem_range).elim
  rw [Finset.sum_congr rfl hinner]
  by_cases hs_mem : s ∈ Finset.range (t + d + 1)
  · rw [Finset.sum_eq_single s]
    · simp; ring
    · intro s' _ hne; simp [Ne.symm hne]
    · exact fun h => (h hs_mem).elim
  · have hnot : ¬ IsClebschGordanTriple t d s := fun htr => hs_mem htr.mem_range
    rw [sixJSymbol_eq_zero_of_not_isClebschGordanTriple hq δ ζ θ (fun h => hnot h.2.1),
      zero_mul, zero_mul,
      Finset.sum_eq_zero fun s' hs' => by simp [show s ≠ s' from fun h => hs_mem (h ▸ hs')],
      mul_zero]

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
  · have heq := congrArg
      (fun Φ => homScalar ((quadrupleRightProjection hq ε δ ζ θ a b c d r s e).comp
        (Φ.comp (quadrupleLeftInclusion hq ε δ ζ θ a b c d p q' e))))
      (congrArg LinearEquiv.toLinearMap (assoc_pentagon ℂ (UqSl2 q)
        (LadderModule q a ε) (LadderModule q b δ) (LadderModule q c ζ) (LadderModule q d θ)))
    simp only [LinearEquiv.coe_trans, toLinearMap_tensorCongr, LinearEquiv.refl_toLinearMap,
      LinearMap.comp_assoc] at heq
    rwa [homScalar_two_step hq ε δ ζ θ htri, homScalar_three_step hq ε δ ζ θ htri, eq_comm] at heq
  · rcases not_and_or.mp htri with hcdr | htri'
    · rw [sixJSymbol_eq_zero_of_not_isClebschGordanTriple hq (ε * δ) ζ θ (fun h => hcdr h.2.2.1),
        mul_zero]
      exact Finset.sum_eq_zero fun _ _ => by
        rw [sixJSymbol_eq_zero_of_not_isClebschGordanTriple hq δ ζ θ (fun h => hcdr h.2.2.1),
          zero_mul, zero_mul]
    rcases not_and_or.mp htri' with hbrs | hase
    · rw [sixJSymbol_eq_zero_of_not_isClebschGordanTriple hq ε δ (ζ * θ) (fun h => hbrs h.2.2.1),
        zero_mul]
      exact Finset.sum_eq_zero fun _ _ => by
        rw [sixJSymbol_eq_zero_of_not_isClebschGordanTriple hq δ ζ θ (fun h => hbrs h.2.2.2),
          zero_mul, zero_mul]
    · rw [sixJSymbol_eq_zero_of_not_isClebschGordanTriple hq ε δ (ζ * θ) (fun h => hase h.2.2.2),
        zero_mul]
      exact Finset.sum_eq_zero fun _ _ => by
        rw [sixJSymbol_eq_zero_of_not_isClebschGordanTriple hq ε (δ * ζ) θ (fun h => hase h.2.2.2),
          mul_zero, zero_mul]

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
    sum_range_eq_sum_fin_sub_two_mul b c _ fun t htr => by
      rw [sixJSymbol_eq_zero_of_not_isClebschGordanTriple hq δ ζ θ (fun h => htr h.1),
        zero_mul, zero_mul]]

/-- Explicit expansion of the quadruple associator `assoc A B (C ⊗ D) ∘ assoc (A ⊗ B) C D` on any
normalized `F`-ladder vector `v_k` (`k : ℤ`) of a left-comb quadruple Clebsch–Gordan channel. -/
theorem assoc_assoc_quadrupleLeftInclusion_vec (hq : IsGenericQuantumParameter q)
    (ε δ ζ θ : ℤˣ) (a b c d p q' e : ℕ) (k : ℤ) :
    assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (Tensor ℂ (UqSl2 q) (LadderModule q c ζ) (LadderModule q d θ))
        (assoc ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
          (LadderModule q c ζ) (LadderModule q d θ)
          (quadrupleLeftInclusion hq ε δ ζ θ a b c d p q' e (vec q e (((ε * δ) * ζ) * θ) k))) =
      ∑ r ∈ Finset.range (c + d + 1), ∑ s ∈ Finset.range (b + r + 1),
        (sixJSymbol hq (ε * δ) ζ θ p c d e q' r * sixJSymbol hq ε δ (ζ * θ) a b r e p s) •
          quadrupleRightInclusion hq ε δ ζ θ a b c d r s e (vec q e (ε * (δ * (ζ * θ))) k) := by
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
  exact Finset.sum_congr rfl fun _ _ => smul_smul _ _ _

end TauCeti.UqSl2

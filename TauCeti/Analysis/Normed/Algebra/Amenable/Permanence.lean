/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Amenable.Diagonal
public import TauCeti.Analysis.Normed.Ring.Quotient.Basic

/-!
# Permanence properties of amenable Banach algebras

This file proves that amenability of normed algebras passes to dense images, to quotients and to
products of two algebras.

**Dense images.** Let `θ : A → B` be a continuous homomorphism of normed algebras with dense
range. Given a Banach `B`-bimodule `E` with actions `L R : B →L[𝕜] E →L[𝕜] E` and a bounded
derivation `D : B → E*`, the pulled-back actions `L ∘ θ`, `R ∘ θ` make `E` an `A`-bimodule and
`D ∘ θ` a bounded derivation of `A` into its dual. If `A` is amenable, then `D ∘ θ` is inner,
implemented by some `φ ∈ E*`; the inner derivation of `B` implemented by `φ` agrees with `D` on the
dense range of `θ`, so equals `D` by continuity. Hence `B` is amenable whenever `A` is
(`TauCeti.IsAmenable.of_denseRange`). The test bimodules of `IsAmenable` live in the universe of
the algebra, so this argument needs `A` and `B` to live in one universe. Over `ℝ` or `ℂ` and for a
Banach algebra `A`, the universe-polymorphic innerness
`IsAmenable.exists_eq_dualAction_sub_dualAction'` removes this restriction
(`TauCeti.IsAmenable.of_denseRange'`). In particular amenability is inherited by images under
continuous surjective homomorphisms, such as quotients of a unital normed algebra by closed
two-sided ideals (`TauCeti.IsAmenable.quotient`).

**Products.** For Banach algebras `A` and `B` over `ℝ` or `ℂ`, the inclusions of the factors carry
bounded approximate diagonals of `A` and `B` to a bounded approximate diagonal of `A × B`
(`TauCeti.IsApproximateDiagonal.prod`), so by Johnson's characterization `A × B` is amenable if
`A` and `B` are. Conversely the projections are continuous surjective homomorphisms, so
`A × B` is amenable if and only if `A` and `B` are (`TauCeti.isAmenable_prod_iff`).

## Main results

* `TauCeti.IsAmenable.of_denseRange` and `TauCeti.IsAmenable.of_denseRange'`: amenability passes
  along continuous homomorphisms with dense range.
* `TauCeti.IsAmenable.quotient`: a quotient of an amenable unital normed algebra by a closed
  two-sided ideal is amenable.
* `TauCeti.IsAmenable.prod` and `TauCeti.isAmenable_prod_iff`: a product of two Banach algebras
  over `ℝ` or `ℂ` is amenable if and only if both factors are.

## References

* V. Runde, *Lectures on Amenability*, Springer, 2002, §2.3 (Proposition 2.3.1).
* B. E. Johnson, *Cohomology in Banach algebras*, Mem. Amer. Math. Soc. 127 (1972).
-/

public section

open Filter ContinuousLinearMap

namespace TauCeti

section DenseRange

variable {𝕜 A B E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [NonUnitalNormedRing B] [NormedSpace 𝕜 B] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let `f : A → B` be a multiplicative bounded operator with dense range, and let
`D : B → E*` be a bounded derivation into the dual of a `B`-bimodule `E`. If every bounded
derivation of `A` into `E*`, for the actions pulled back along `f`, is inner, then so is `D`. -/
private theorem exists_eq_dualAction_sub_dualAction_of_denseRange (f : A →L[𝕜] B)
    (hf : ∀ x y, f (x * y) = f x * f y) (hd : DenseRange f) {L R : B →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : B →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a))
    (hA : ∀ L' R' : A →L[𝕜] E →L[𝕜] E, (∀ a b x, L' (a * b) x = L' a (L' b x)) →
      (∀ a b x, R' (a * b) x = R' b (R' a x)) → (∀ a b x, L' a (R' b x) = R' b (L' a x)) →
      ∀ D' : A →L[𝕜] StrongDual 𝕜 E,
        (∀ a b, D' (a * b) = dualAction R' a (D' b) + dualAction L' b (D' a)) →
          ∃ φ : StrongDual 𝕜 E, ∀ a, D' a = dualAction R' a φ - dualAction L' a φ) :
    ∃ φ : StrongDual 𝕜 E, ∀ b, D b = dualAction R b φ - dualAction L b φ := by
  obtain ⟨φ, hφ⟩ := hA (L ∘L f) (R ∘L f) (fun a b x ↦ by simp [hf, hL])
    (fun a b x ↦ by simp [hf, hR]) (fun a b x ↦ by simp [hLR]) (D ∘L f)
    (fun a b ↦ by simpa [dualAction_apply, hf] using hD (f a) (f b))
  have heq : (D : B → StrongDual 𝕜 E) = fun b ↦ dualAction R b φ - dualAction L b φ :=
    hd.equalizer D.continuous ((dualAction R).flip φ - (dualAction L).flip φ).continuous <|
      funext fun a ↦ by simpa [dualAction_apply] using hφ a
  exact ⟨φ, fun b ↦ congr_fun heq b⟩

end DenseRange

section SameUniverse

universe u

variable {𝕜 : Type*} {A B : Type u} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [NonUnitalNormedRing B] [NormedSpace 𝕜 B]

/-- **Amenability passes to dense images.** If `θ : A → B` is a continuous homomorphism of normed
algebras with dense range and `A` is amenable, then `B` is amenable. Here `A` and `B` live in one
universe; see `TauCeti.IsAmenable.of_denseRange'` for Banach algebras over `ℝ` or `ℂ` in arbitrary
universes. -/
theorem IsAmenable.of_denseRange (h : IsAmenable 𝕜 A) (θ : A →ₙₐ[𝕜] B) (hθ : Continuous θ)
    (hd : DenseRange θ) : IsAmenable 𝕜 B :=
  isAmenable_def.2 fun _ _ _ _ _ _ hL hR hLR D hD ↦
    exists_eq_dualAction_sub_dualAction_of_denseRange ⟨(θ : A →ₗ[𝕜] B), hθ⟩ (map_mul θ) hd hL hR
      hLR D hD fun _ _ hL' hR' hLR' D' hD' ↦
        h.exists_eq_dualAction_sub_dualAction hL' hR' hLR' D' hD'

end SameUniverse

section RCLike

variable {𝕜 A B : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A] [NonUnitalNormedRing B]
  [NormedSpace 𝕜 B]

/-- **Amenability passes to dense images**, for a Banach algebra `A` over `ℝ` or `ℂ` and a normed
algebra `B` in an arbitrary universe: if `θ : A → B` is a continuous homomorphism with dense range
and `A` is amenable, then `B` is amenable. -/
theorem IsAmenable.of_denseRange' (h : IsAmenable 𝕜 A) (θ : A →ₙₐ[𝕜] B) (hθ : Continuous θ)
    (hd : DenseRange θ) : IsAmenable 𝕜 B :=
  isAmenable_def.2 fun _ _ _ _ _ _ hL hR hLR D hD ↦
    exists_eq_dualAction_sub_dualAction_of_denseRange ⟨(θ : A →ₗ[𝕜] B), hθ⟩ (map_mul θ) hd hL hR
      hLR D hD fun _ _ hL' hR' hLR' D' hD' ↦
        h.exists_eq_dualAction_sub_dualAction' hL' hR' hLR' D' hD'

variable [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B] [CompleteSpace B]

/-- **Amenability of products.** The product of two amenable Banach algebras over `ℝ` or `ℂ` is
amenable. -/
theorem IsAmenable.prod (hA : IsAmenable 𝕜 A) (hB : IsAmenable 𝕜 B) : IsAmenable 𝕜 (A × B) := by
  obtain ⟨C₁, l₁, h₁, hC₁⟩ := hA.exists_isApproximateDiagonal
  obtain ⟨C₂, l₂, h₂, hC₂⟩ := hB.exists_isApproximateDiagonal
  refine isAmenable_iff_exists_isApproximateDiagonal.2
    ⟨‖CompletedProjectiveTensor.mapL (.inl 𝕜 A B) (.inl 𝕜 A B)‖ * C₁ +
      ‖CompletedProjectiveTensor.mapL (.inr 𝕜 A B) (.inr 𝕜 A B)‖ * C₂, _, h₁.prod h₂,
      eventually_map.2 ((hC₁.prod_mk hC₂).mono fun m hm ↦ ?_)⟩
  exact (norm_add_le _ _).trans <| add_le_add
    ((le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hm.1 (norm_nonneg _)))
    ((le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hm.2 (norm_nonneg _)))

/-- **Amenability of products.** A product of two Banach algebras over `ℝ` or `ℂ` is amenable if
and only if both factors are. -/
theorem isAmenable_prod_iff : IsAmenable 𝕜 (A × B) ↔ IsAmenable 𝕜 A ∧ IsAmenable 𝕜 B :=
  ⟨fun h ↦ ⟨h.of_denseRange' (NonUnitalAlgHom.fst 𝕜 A B) continuous_fst
      Prod.fst_surjective.denseRange,
    h.of_denseRange' (NonUnitalAlgHom.snd 𝕜 A B) continuous_snd Prod.snd_surjective.denseRange⟩,
    fun h ↦ h.1.prod h.2⟩

end RCLike

section Quotient

variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [NormedRing R] [NormedAlgebra 𝕜 R]

/-- **Amenability passes to quotients.** The quotient of an amenable unital normed algebra by a
closed two-sided ideal is amenable. -/
theorem IsAmenable.quotient (h : IsAmenable 𝕜 R) (I : Ideal R) [I.IsTwoSided]
    [IsClosed (I : Set R)] : IsAmenable 𝕜 (R ⧸ I) :=
  h.of_denseRange (Ideal.Quotient.mkA 𝕜 I : R →ₐ[𝕜] R ⧸ I).toNonUnitalAlgHom
    (Ideal.Quotient.mkA 𝕜 I).continuous (Ideal.Quotient.mkA_surjective 𝕜 I).denseRange

end Quotient

end TauCeti

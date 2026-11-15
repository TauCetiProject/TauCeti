/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The even unitary carrier as a symplectic group

An algebra isomorphism from the even Clifford algebra `C₀` to a matrix algebra of even size which
carries reversal `σ` to the standard symplectic adjoint `X ↦ J⁻¹ Xᵀ J = -(J Xᵀ J)` identifies the
reverse-unitary carrier `U(C₀, σ)` with Mathlib's `Matrix.symplecticGroup`. This is a
specialisation of `CliffordAlgebra.evenUnitaryGroupEquivOfAlgEquiv`, valid over any commutative
ring and with no assumption on the dimension.

When `C₀` only becomes a matrix algebra after extending scalars to an `R`-algebra `A`, the same
transport is applied there: an isomorphism `C₀ ⊗ A ≃ M(A)` carrying the extended reversal to the
symplectic adjoint maps `U(C₀, σ)` into the symplectic group over `A`. For a faithful flat
extension this map is injective, and its image is exactly the set of symplectic matrices whose
preimage in `C₀ ⊗ A` comes from `C₀`. This is how `U(C₀, σ)` is read as the group `Sp(C₀, σ)` of
a twisted form of the symplectic group.

## Main definitions

* `CliffordAlgebra.evenUnitaryGroupEquivSymplecticGroup`: an algebra isomorphism from `C₀` to a
  matrix algebra carrying `σ` to the symplectic adjoint identifies `U(C₀, σ)` with the symplectic
  group.
* `CliffordAlgebra.evenUnitaryGroupToSymplecticGroup`: the same after extension of scalars, a
  homomorphism from `U(C₀, σ)` to the symplectic group over the extension.

## Main results

* `CliffordAlgebra.evenUnitaryGroupToSymplecticGroup_injective`: the map is injective for faithful
  flat extensions.
* `CliffordAlgebra.mem_range_evenUnitaryGroupToSymplecticGroup_iff`: its image consists of the
  symplectic matrices whose preimage under the splitting is defined over `R`.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §8.D.
-/

public section

open Matrix

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (Q : QuadraticForm R M)
  {l : Type*} [Fintype l] [DecidableEq l]

/-- An algebra isomorphism from the even Clifford algebra to a matrix algebra of even size which
carries reversal to the symplectic adjoint `X ↦ -(J Xᵀ J)` identifies the even unitary carrier
`U(C₀, σ)` with the symplectic group. -/
noncomputable def evenUnitaryGroupEquivSymplecticGroup
    (e : even Q ≃ₐ[R] Matrix (l ⊕ l) (l ⊕ l) R)
    (he : ∀ x, e (reverseEven Q x) = -(J l R * (e x)ᵀ * J l R)) :
    evenUnitaryGroup Q ≃* symplecticGroup l R :=
  evenUnitaryGroupEquivOfAlgEquiv Q e (· ∈ symplecticGroup l R) (symplecticGroup l R).subtype
    Subtype.val_injective (fun a ha => ⟨a, ha⟩) (fun _ _ => rfl) (fun g => g.2) fun x => by
      rw [SymplecticGroup.mem_iff_neg_J_mul_transpose_mul_J_mul_eq_one, ← Matrix.neg_mul, ← he,
        ← map_mul, ← map_one e, e.injective.eq_iff]

/-- The symplectic transport applies the algebra isomorphism to the even Clifford value. -/
@[simp]
theorem coe_evenUnitaryGroupEquivSymplecticGroup_apply
    (e : even Q ≃ₐ[R] Matrix (l ⊕ l) (l ⊕ l) R)
    (he : ∀ x, e (reverseEven Q x) = -(J l R * (e x)ᵀ * J l R)) (x : evenUnitaryGroup Q) :
    (evenUnitaryGroupEquivSymplecticGroup Q e he x : Matrix (l ⊕ l) (l ⊕ l) R) =
      e (evenUnitaryGroupEvenPart Q x) := by
  rw [evenUnitaryGroupEquivSymplecticGroup]
  exact coe_evenUnitaryGroupEquivOfAlgEquiv_apply Q e _ (symplecticGroup l R).subtype _ _ _ _ _ x

/-- The inverse symplectic transport applies the inverse algebra isomorphism. -/
@[simp]
theorem evenUnitaryGroupEvenPart_evenUnitaryGroupEquivSymplecticGroup_symm_apply
    (e : even Q ≃ₐ[R] Matrix (l ⊕ l) (l ⊕ l) R)
    (he : ∀ x, e (reverseEven Q x) = -(J l R * (e x)ᵀ * J l R)) (g : symplecticGroup l R) :
    evenUnitaryGroupEvenPart Q ((evenUnitaryGroupEquivSymplecticGroup Q e he).symm g) =
      e.symm g := by
  rw [evenUnitaryGroupEquivSymplecticGroup]
  exact evenUnitaryGroupEquivOfAlgEquiv_symm_apply_evenPart Q e _ (symplecticGroup l R).subtype
    _ _ _ _ _ g

/-! ### After extension of scalars -/

section BaseChange

variable {A : Type*} [CommRing A] [Algebra R A] [Invertible (2 : R)]

/-- An algebra isomorphism from the scalar-extended even Clifford algebra `C₀ ⊗ A` to a matrix
algebra of even size which carries reversal to the symplectic adjoint `X ↦ -(J Xᵀ J)` maps the
even unitary carrier `U(C₀, σ)` into the symplectic group over `A`: extend scalars by
`CliffordAlgebra.evenUnitaryGroupBaseChange`, then apply
`CliffordAlgebra.evenUnitaryGroupEquivSymplecticGroup`. -/
noncomputable def evenUnitaryGroupToSymplecticGroup
    (e : even (Q.baseChange A) ≃ₐ[A] Matrix (l ⊕ l) (l ⊕ l) A)
    (he : ∀ x, e (reverseEven (Q.baseChange A) x) = -(J l A * (e x)ᵀ * J l A)) :
    evenUnitaryGroup Q →* symplecticGroup l A :=
  (evenUnitaryGroupEquivSymplecticGroup (Q.baseChange A) e he).toMonoidHom.comp
    (evenUnitaryGroupBaseChange Q)

/-- The symplectic matrix attached to an even unitary element is the splitting applied to its
scalar extension. -/
@[simp]
theorem coe_evenUnitaryGroupToSymplecticGroup_apply
    (e : even (Q.baseChange A) ≃ₐ[A] Matrix (l ⊕ l) (l ⊕ l) A)
    (he : ∀ x, e (reverseEven (Q.baseChange A) x) = -(J l A * (e x)ᵀ * J l A))
    (x : evenUnitaryGroup Q) :
    (evenUnitaryGroupToSymplecticGroup Q e he x : Matrix (l ⊕ l) (l ⊕ l) A) =
      e (evenUnitaryGroupEvenPart (Q.baseChange A) (evenUnitaryGroupBaseChange Q x)) := by
  simp [evenUnitaryGroupToSymplecticGroup]

/-- The map from `U(C₀, σ)` to the symplectic group over a faithful flat extension is
injective. -/
theorem evenUnitaryGroupToSymplecticGroup_injective [FaithfulSMul R A]
    [Module.Flat R (CliffordAlgebra Q)]
    (e : even (Q.baseChange A) ≃ₐ[A] Matrix (l ⊕ l) (l ⊕ l) A)
    (he : ∀ x, e (reverseEven (Q.baseChange A) x) = -(J l A * (e x)ᵀ * J l A)) :
    Function.Injective (evenUnitaryGroupToSymplecticGroup Q e he) :=
  (evenUnitaryGroupEquivSymplecticGroup (Q.baseChange A) e he).injective.comp
    (evenUnitaryGroupBaseChange_injective Q)

/-- **The image of `U(C₀, σ)` in the symplectic group over a splitting extension.** Over a
faithful flat extension `A` splitting `(C₀, σ)` symplectically, a symplectic matrix `g` comes from
an even unitary element exactly when its preimage in `C₀ ⊗ A` lies in the image of `C₀`. -/
theorem mem_range_evenUnitaryGroupToSymplecticGroup_iff [FaithfulSMul R A]
    [Module.Flat R (CliffordAlgebra Q)]
    (e : even (Q.baseChange A) ≃ₐ[A] Matrix (l ⊕ l) (l ⊕ l) A)
    (he : ∀ x, e (reverseEven (Q.baseChange A) x) = -(J l A * (e x)ᵀ * J l A))
    (g : symplecticGroup l A) :
    g ∈ (evenUnitaryGroupToSymplecticGroup Q e he).range ↔
      ∃ y ∈ even Q, ofBaseChangeAux A Q y = (e.symm g : CliffordAlgebra (Q.baseChange A)) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, evenUnitaryGroup.mem_even Q x.2, by simp⟩
  · rintro ⟨y, hy, hyg⟩
    -- The unit of `C₀ ⊗ A` corresponding to `g`; its reverse norms are one.
    set u := (evenUnitaryGroupEquivSymplecticGroup (Q.baseChange A) e he).symm g
    have hu : ((u : (CliffordAlgebra (Q.baseChange A))ˣ) : CliffordAlgebra (Q.baseChange A)) =
        ofBaseChangeAux A Q y := by
      rw [hyg, ← coe_evenUnitaryGroupEvenPart,
        evenUnitaryGroupEvenPart_evenUnitaryGroupEquivSymplecticGroup_symm_apply]
    have hinj := ofBaseChangeAux_injective (A := A) Q
    have h₁ : reverse y * y = 1 := hinj <| by
      rw [map_mul, map_one, ofBaseChangeAux_reverse, ← hu, evenUnitaryGroup.reverse_mul_self]
    have h₂ : y * reverse y = 1 := hinj <| by
      rw [map_mul, map_one, ofBaseChangeAux_reverse, ← hu, evenUnitaryGroup.self_mul_reverse]
    let x : (CliffordAlgebra Q)ˣ := ⟨y, reverse y, h₂, h₁⟩
    have hx : x ∈ evenUnitaryGroup Q :=
      (evenUnitaryGroup.mem_iff_reverse_mul_self_eq_one Q).mpr ⟨hy, h₁⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    have hbc : evenUnitaryGroupBaseChange Q ⟨x, hx⟩ = u :=
      Subtype.ext (Units.ext (by rw [coe_evenUnitaryGroupBaseChange_apply, hu]))
    simp only [evenUnitaryGroupToSymplecticGroup, MonoidHom.comp_apply, hbc, u]
    exact (evenUnitaryGroupEquivSymplecticGroup (Q.baseChange A) e he).apply_symm_apply g

end BaseChange

end CliffordAlgebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Equiv.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant
public import TauCeti.LinearAlgebra.QuadraticForm.Transport

/-!
# Transport of isometry classes along isomorphisms of fields

A ring isomorphism `τ : K ≃+* L` of fields carries a diagonal presentation `⟨a₁, …, aₙ⟩` over `K`
to the presentation `⟨τ a₁, …, τ aₙ⟩` over `L`. The presented form over `L` is the transport
(`QuadraticMap.transport`) of the presented form over `K` along the coordinatewise semilinear
equivalence `(Fin n → K) ≃ₛₗ[τ] (Fin n → L)`, so isometric presentations go to isometric
presentations and the operation descends to the isometry classes of regular forms as
`TauCeti.RegularFormClass.map τ`. It is a bijection, with inverse `RegularFormClass.map τ.symm`,
and it is additive.

The class of the transport of a regular form along any `τ`-semilinear equivalence is the image of
its class (`QuadraticForm.formClass_transport`). The rank is unchanged and the discriminant is
pushed forward along the map of square-class groups induced by `τ`
(`TauCeti.RegularFormClass.discr_map`). This is what lets the invariants of a regular form over one
field be read over an isomorphic copy of it, for instance over a completion of an isomorphic number
field, or over a copy of the field in another universe.

## Main definitions

* `TauCeti.RegularFormPresentation.map`: the presentation whose weights are the images of the
  original weights under a ring isomorphism.
* `TauCeti.RegularFormClass.map`: the induced map of isometry classes.

## Main results

* `TauCeti.presentedForm_map`: the presented form of the mapped presentation is the transport of the
  presented form along the coordinatewise semilinear equivalence.
* `TauCeti.RegularFormClass.map_map`, `TauCeti.RegularFormClass.map_refl`,
  `TauCeti.RegularFormClass.map_symm_map`, `TauCeti.RegularFormClass.map_map_symm`: functoriality,
  so that `RegularFormClass.map τ` is a bijection.
* `TauCeti.RegularFormClass.rank_map`, `TauCeti.RegularFormClass.map_add`,
  `TauCeti.RegularFormClass.map_zero`: the map preserves the rank and the orthogonal sum.
* `TauCeti.RegularFormClass.discr_map`: the discriminant of the image is the image of the
  discriminant.
* `QuadraticForm.formClass_transport`: the class of a transported regular form is the image of its
  class.
-/

public section
noncomputable section

open QuadraticMap

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace TauCeti

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L]

/-! ### Presentations -/

-- The body is exposed so that the rank of the mapped presentation is definitionally that of `p`:
-- `presentedForm_map` compares forms on `Fin (p.map τ).1 → L` and on `Fin p.1 → L`.
/-- The presentation whose weights are the images of the weights of `p` under a ring isomorphism
`τ : K ≃+* L`. The rank is unchanged. -/
@[expose] def RegularFormPresentation.map (τ : K ≃+* L) (p : RegularFormPresentation K) :
    RegularFormPresentation L :=
  ⟨p.1, fun i ↦ Units.map (τ : K →* L) (p.2 i)⟩

/-- Mapping a presentation keeps its rank. -/
@[simp]
theorem RegularFormPresentation.fst_map (τ : K ≃+* L) (p : RegularFormPresentation K) :
    (p.map τ).1 = p.1 :=
  (rfl)

/-- The weights of a mapped presentation are the images of the original weights. -/
@[simp]
theorem RegularFormPresentation.map_apply (τ : K ≃+* L) (p : RegularFormPresentation K)
    (i : Fin (p.map τ).1) :
    (p.map τ).2 i = Units.map (τ : K →* L) (p.2 i) :=
  (rfl)

/-- The weight product of a mapped presentation is the image of the original weight product. -/
theorem RegularFormPresentation.prod_map (τ : K ≃+* L) (p : RegularFormPresentation K) :
    ∏ i, (p.map τ).2 i = Units.map (τ : K →* L) (∏ i, p.2 i) :=
  (map_prod (Units.map (τ : K →* L)) _ _).symm

/-- **Presented forms transport along `τ`**: the form presented by `⟨τ a₁, …, τ aₙ⟩` is the
transport of the form presented by `⟨a₁, …, aₙ⟩` along the coordinatewise semilinear equivalence
`(Fin n → K) ≃ₛₗ[τ] (Fin n → L)`. -/
theorem presentedForm_map (τ : K ≃+* L) (p : RegularFormPresentation K) :
    presentedForm (p.map τ) =
      (presentedForm p).transport (LinearEquiv.piCongrRightₛₗ fun _ ↦ τ.toSemilinearEquiv) := by
  obtain ⟨n, w⟩ := p
  refine (presentedForm_eq_weightedSumSquares_coe fun i ↦ Units.map (τ : K →* L) (w i)).trans ?_
  rw [presentedForm_eq_weightedSumSquares_coe, QuadraticMap.transport_weightedSumSquares]
  simp

/-! ### Isometry classes -/

/-- **Transport of isometry classes along a ring isomorphism** `τ : K ≃+* L`: the class over `L`
presented by the images under `τ` of the weights of any presentation over `K`. -/
def RegularFormClass.map (τ : K ≃+* L) : RegularFormClass K → RegularFormClass L :=
  Quotient.map (RegularFormPresentation.map τ) fun p q h ↦ regularFormSetoid_iff.mpr <| by
    rw [presentedForm_map, presentedForm_map]
    exact (regularFormSetoid_iff.mp h).transport _ _

/-- The transported class is computed on presentations by mapping the weights. -/
@[simp]
theorem RegularFormClass.map_mk (τ : K ≃+* L) (p : RegularFormPresentation K) :
    RegularFormClass.map τ (Quotient.mk (regularFormSetoid K) p) =
      Quotient.mk (regularFormSetoid L) (p.map τ) :=
  (rfl)

/-- Transport along the identity is the identity. -/
@[simp]
theorem RegularFormClass.map_refl (x : RegularFormClass K) :
    RegularFormClass.map (RingEquiv.refl K) x = x := by
  refine Quotient.inductionOn x fun p ↦ ?_
  rw [RegularFormClass.map_mk]
  congr 1

/-- Transporting along `τ` and then along `τ'` is transporting along `τ.trans τ'`. -/
@[simp]
theorem RegularFormClass.map_map {M : Type w} [Field M] (τ : K ≃+* L) (τ' : L ≃+* M)
    (x : RegularFormClass K) :
    RegularFormClass.map τ' (RegularFormClass.map τ x) = RegularFormClass.map (τ.trans τ') x := by
  refine Quotient.inductionOn x fun p ↦ ?_
  rw [RegularFormClass.map_mk, RegularFormClass.map_mk, RegularFormClass.map_mk]
  congr 1

/-- Transporting along `τ` and then back along `τ.symm` is the identity. -/
-- Not `@[simp]`: `RegularFormClass.map_map`, `RingEquiv.self_trans_symm` and
-- `RegularFormClass.map_refl` already prove it.
theorem RegularFormClass.map_symm_map (τ : K ≃+* L) (x : RegularFormClass K) :
    RegularFormClass.map τ.symm (RegularFormClass.map τ x) = x := by
  rw [RegularFormClass.map_map, RingEquiv.self_trans_symm, map_refl]

/-- Transporting along `τ.symm` and then along `τ` is the identity. -/
-- Not `@[simp]`: `RegularFormClass.map_map`, `RingEquiv.symm_trans_self` and
-- `RegularFormClass.map_refl` already prove it.
theorem RegularFormClass.map_map_symm (τ : K ≃+* L) (x : RegularFormClass L) :
    RegularFormClass.map τ (RegularFormClass.map τ.symm x) = x := by
  rw [RegularFormClass.map_map, RingEquiv.symm_trans_self, map_refl]

/-- Transport of isometry classes along a ring isomorphism is injective. -/
theorem RegularFormClass.map_injective (τ : K ≃+* L) :
    Function.Injective (RegularFormClass.map τ) :=
  Function.LeftInverse.injective (RegularFormClass.map_symm_map τ)

/-- Transport of isometry classes along a ring isomorphism is surjective. -/
theorem RegularFormClass.map_surjective (τ : K ≃+* L) :
    Function.Surjective (RegularFormClass.map τ) :=
  Function.RightInverse.surjective (RegularFormClass.map_map_symm τ)

/-- Transport preserves the rank of a class. -/
@[simp]
theorem RegularFormClass.rank_map (τ : K ≃+* L) (x : RegularFormClass K) :
    (RegularFormClass.map τ x).rank = x.rank := by
  refine Quotient.inductionOn x fun p ↦ ?_
  rw [RegularFormClass.map_mk, RegularFormClass.rank_mk, RegularFormClass.rank_mk,
    RegularFormPresentation.fst_map]

/-- Transport commutes with the orthogonal sum of classes. -/
@[simp]
protected theorem RegularFormClass.map_add (τ : K ≃+* L) (x y : RegularFormClass K) :
    RegularFormClass.map τ (x + y) = RegularFormClass.map τ x + RegularFormClass.map τ y := by
  refine Quotient.inductionOn₂ x y fun p q ↦ ?_
  rw [RegularFormClass.mk_add_mk, RegularFormClass.map_mk, RegularFormClass.map_mk,
    RegularFormClass.map_mk, RegularFormClass.mk_add_mk, RegularFormPresentation.append_def,
    RegularFormPresentation.append_def]
  refine congrArg _ (RegularFormPresentation.ext rfl fun i ↦ ?_)
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp [RegularFormPresentation.map]

/-- Transport takes the rank-zero class to the rank-zero class. -/
@[simp]
protected theorem RegularFormClass.map_zero (τ : K ≃+* L) :
    RegularFormClass.map τ (0 : RegularFormClass K) = 0 := by
  rw [RegularFormClass.zero_def, RegularFormClass.map_mk, RegularFormClass.zero_def]
  exact congrArg _ (RegularFormPresentation.ext rfl fun i ↦ i.elim0)

/-- **The discriminant commutes with transport**: the discriminant of the transported class is the
image of the discriminant under the map of square-class groups induced by `τ`. -/
@[simp]
theorem RegularFormClass.discr_map [Invertible (2 : K)] [Invertible (2 : L)] (τ : K ≃+* L)
    (x : RegularFormClass K) :
    RegularFormClass.discr (RegularFormClass.map τ x) =
      (τ : K →+* L).squareClassMap (RegularFormClass.discr x) := by
  refine Quotient.inductionOn x fun p ↦ ?_
  rw [RegularFormClass.map_mk, RegularFormClass.discr_mk, RegularFormClass.discr_mk,
    RingHom.squareClassMap_apply, RegularFormPresentation.prod_map]
  -- the two sides differ only in how `τ` is coerced to a monoid homomorphism
  rfl

end TauCeti

namespace QuadraticForm

open TauCeti

variable {K : Type*} {L : Type*} [Field K] [Field L] [Invertible (2 : K)] [Invertible (2 : L)]
variable {V : Type*} {V' : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup V'] [Module L V'] [FiniteDimensional L V']

/-- **The class of a transported form is the transported class**: for a regular form `Q` over `K`
and a semilinear equivalence `f : V ≃ₛₗ[τ] V'` over a ring isomorphism `τ : K ≃+* L`, the class of
`Q.transport f` is the image under `RegularFormClass.map τ` of the class of `Q`. -/
theorem formClass_transport (τ : K ≃+* L) (f : V ≃ₛₗ[(τ : K →+* L)] V')
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    formClass (Q.transport f) ((nondegenerate_transport_iff f Q).mpr hQ) =
      RegularFormClass.map τ (formClass Q hQ) := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p hp, RegularFormClass.map_mk,
    formClass_mk _ _ (p.map τ) (by rw [presentedForm_map]; exact hp.transport _ _)]

end QuadraticForm

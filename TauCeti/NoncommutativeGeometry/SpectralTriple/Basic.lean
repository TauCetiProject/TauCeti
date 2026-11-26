/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.CompactResolvent
public import TauCeti.Topology.Algebra.Module.LinearPMap.Sylvester
import TauCeti.Analysis.InnerProductSpace.LinearPMap.Eigenbasis

/-!
# Spectral triples

A (unital) *spectral triple* `(A, H, D)` consists of a Hilbert space `H`, a unital
`*`-representation `π : A → B(H)`, and a self-adjoint operator `D : H →ₗ.[ℂ] H` with compact
resolvent such that `π(a)` preserves `D(D)` and `[D, π(a)]` extends to a bounded operator on `H`.
An *even* spectral triple adds a self-adjoint unitary grading `γ` commuting with `π` and
anticommuting with `D` on `D(D)`.

## Main definitions & results

* `TauCeti.SpectralTriple`, `TauCeti.EvenSpectralTriple`: odd and even spectral triples.
* `TauCeti.SpectralTriple.separableSpace`: `H` is automatically separable.
* `TauCeti.SpectralTriple.commutator`, `commutator_mul`, `commutator_star`,
  `sylvesterEquation_commutator`: the `ℂ`-linear derivation `a ↦ [D, π(a)]`, its Sylvester
  equation, and graph-norm bounds (`norm_operator_rep_le`).
* `SpectralTriple.conj`, `SpectralTriple.comap`, `SpectralTriple.ofFiniteDimensional` (and their
  even counterparts): unitary transport, algebra pullback, and finite-dimensional triples.

## References

* A. Connes, *Noncommutative Geometry*, Academic Press (1994), Chapter IV, §2.
* J. M. Gracia-Bondía, J. C. Várilly, H. Figueroa, *Elements of Noncommutative Geometry*,
  Birkhäuser (2001), Chapter 10.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace TauCeti

variable (A : Type*) [Semiring A] [Algebra ℂ A] [Star A]
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An odd (unital) **spectral triple** over the complex `*`-algebra `A` on the Hilbert space `H`:
a unital `*`-representation `rep` of `A` by bounded operators on `H` and an unbounded self-adjoint
operator `operator` (Connes' `D`) with compact resolvent such that every `π(a)` preserves the
domain of `D` and the commutator `[D, π(a)]` extends from `D(D)` to a bounded operator on `H`.

Because `D` is self-adjoint with compact resolvent, `H` is automatically separable
(`SpectralTriple.separableSpace`). -/
@[ext]
structure SpectralTriple where
  /-- The unital `*`-representation `π` of `A` by bounded operators on `H`. -/
  rep : A →⋆ₐ[ℂ] H →L[ℂ] H
  /-- The unbounded Dirac operator `D` of the spectral triple. -/
  operator : H →ₗ.[ℂ] H
  isSelfAdjoint_operator : IsSelfAdjoint operator
  hasCompactResolvent_operator : operator.HasCompactResolvent
  exists_bounded_commutator (a : A) :
    ∃ C : H →L[ℂ] H, LinearPMap.SylvesterEquation operator operator (rep a) C

/-- An **even spectral triple** over `A` on `H`: a spectral triple together with a grading `γ`, a
self-adjoint unitary involution of `H` that commutes with the representation `π`, preserves the
domain of `D`, and anticommutes with `D` on its domain. -/
@[ext]
structure EvenSpectralTriple extends SpectralTriple A H where
  /-- The grading operator `γ`. -/
  grading : H →L[ℂ] H
  isSelfAdjoint_grading : IsSelfAdjoint grading
  grading_mul_grading : grading * grading = 1
  commute_grading_rep (a : A) : Commute grading (rep a)
  grading_mem_domain {x : H} (hx : x ∈ operator.domain) : grading x ∈ operator.domain
  grading_apply_operator (x : operator.domain) :
    grading (operator x) = -operator ⟨grading x, grading_mem_domain x.property⟩

variable {A H}

/-! ### Odd spectral triples -/

namespace SpectralTriple

variable (S : SpectralTriple A H)

/-- Every operator `π(a)` in the representation preserves the domain of `D`. -/
theorem rep_mem_domain (a : A) {x : H} (hx : x ∈ S.operator.domain) :
    S.rep a x ∈ S.operator.domain :=
  (S.exists_bounded_commutator a).choose_spec.mapsTo_domain ⟨x, hx⟩

/-- The domain of the Dirac operator of a spectral triple is dense in `H`. -/
theorem dense_domain : Dense (S.operator.domain : Set H) :=
  S.isSelfAdjoint_operator.dense_domain

/-- The Hilbert space of a spectral triple is automatically separable. -/
theorem separableSpace (S : SpectralTriple A H) : TopologicalSpace.SeparableSpace H :=
  S.isSelfAdjoint_operator.separableSpace_of_hasCompactResolvent S.hasCompactResolvent_operator

private theorem eq_choose_commutator {a : A} {C : H →L[ℂ] H}
    (hC : LinearPMap.SylvesterEquation S.operator S.operator (S.rep a) C) :
    C = (S.exists_bounded_commutator a).choose := by
  ext x
  exact congrFun (Continuous.ext_on S.dense_domain C.continuous
    (S.exists_bounded_commutator a).choose.continuous fun y hy ↦ (hC.equation ⟨y, hy⟩).symm.trans
      ((S.exists_bounded_commutator a).choose_spec.equation ⟨y, hy⟩)) x

/-- The canonical bounded extension `a ↦ [D, π(a)]` of the commutator with `D`, as a `ℂ`-linear
map `A →ₗ[ℂ] (H →L[ℂ] H)`. -/
def commutator : A →ₗ[ℂ] (H →L[ℂ] H) where
  toFun a := (S.exists_bounded_commutator a).choose
  map_add' a b := (S.eq_choose_commutator <| by
    simpa only [map_add] using (S.exists_bounded_commutator a).choose_spec.add
      (S.exists_bounded_commutator b).choose_spec).symm
  map_smul' c a := (S.eq_choose_commutator <| by
    simpa only [map_smul, RingHom.id_apply] using
      (S.exists_bounded_commutator a).choose_spec.smul c).symm

/-- The canonical commutator `S.commutator a` solves the domain-aware Sylvester equation
`D π(a) - π(a) D = [D, π(a)]`. -/
theorem sylvesterEquation_commutator (a : A) :
    LinearPMap.SylvesterEquation S.operator S.operator (S.rep a) (S.commutator a) :=
  (S.exists_bounded_commutator a).choose_spec

/-- On the domain of `D`, `S.commutator a` agrees with `D (π(a) x) - π(a) (D x)`. -/
theorem commutator_apply_domain (a : A) (x : S.operator.domain) :
    S.operator ⟨S.rep a x, S.rep_mem_domain a x.property⟩ - S.rep a (S.operator x) =
      S.commutator a x :=
  (S.sylvesterEquation_commutator a).equation x

/-- Rewritten form of `commutator_apply_domain`: `D (π(a) x) = π(a) (D x) + [D, π(a)] x`. -/
theorem operator_rep_apply (a : A) (x : S.operator.domain) :
    S.operator ⟨S.rep a x, S.rep_mem_domain a x.property⟩ =
      S.rep a (S.operator x) + S.commutator a x :=
  eq_add_of_sub_eq' (S.commutator_apply_domain a x)

/-- Uniqueness of the bounded commutator extension: any bounded operator agreeing with `[D, π(a)]`
on `D(D)` equals `S.commutator a`. -/
theorem eq_commutator_of_domain {a : A} {C : H →L[ℂ] H}
    (hC : ∀ x : S.operator.domain,
      S.operator ⟨S.rep a x, S.rep_mem_domain a x.property⟩ - S.rep a (S.operator x) = C x) :
    C = S.commutator a :=
  S.eq_choose_commutator ⟨fun x ↦ S.rep_mem_domain a x.property, hC⟩

/-- The commutator of `D` with the unit `π(1) = 1` vanishes. -/
@[simp]
theorem commutator_one : S.commutator 1 = 0 := by
  refine (S.eq_commutator_of_domain fun x ↦ ?_).symm
  have h1 : (⟨S.rep 1 x, S.rep_mem_domain 1 x.property⟩ : S.operator.domain) = x :=
    Subtype.ext (by simp)
  rw [h1, map_one, one_apply_eq_self, sub_self, zero_apply]

/-- **Leibniz rule.** The commutator map satisfies
`[D, π(a b)] = [D, π(a)] π(b) + π(a) [D, π(b)]`. -/
theorem commutator_mul (a b : A) :
    S.commutator (a * b) = S.commutator a * S.rep b + S.rep a * S.commutator b := by
  refine (S.eq_commutator_of_domain fun x ↦ ?_).symm
  have h1 := S.commutator_apply_domain a ⟨S.rep b x, S.rep_mem_domain b x.property⟩
  have h2 := S.commutator_apply_domain b x
  simp only [add_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, map_mul]
  dsimp only at h1; rw [← h1, ← h2, map_sub]; abel

/-- **Adjoint identity.** For every `a : A`, `[D, π(a*)] = -[D, π(a)]*`. -/
theorem commutator_star (a : A) :
    S.commutator (star a) = -star (S.commutator a) := by
  refine (S.eq_commutator_of_domain fun x ↦ ?_).symm
  refine ext_inner_left ℂ <| congrFun <| Continuous.ext_on S.dense_domain
    (continuous_id.inner continuous_const) (continuous_id.inner continuous_const) fun y hy ↦ ?_
  have hπ_adj : S.rep (star a) = (S.rep a).adjoint := by
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  have h1 : ⟪y, S.operator ⟨S.rep (star a) x, S.rep_mem_domain (star a) x.property⟩⟫_ℂ =
      ⟪S.rep a (S.operator ⟨y, hy⟩), (x : H)⟫_ℂ := by
    rw [← S.isSelfAdjoint_operator.isFormalAdjoint ⟨y, hy⟩
      ⟨S.rep (star a) x, S.rep_mem_domain (star a) x.property⟩]
    dsimp only
    rw [hπ_adj, ContinuousLinearMap.adjoint_inner_right]
  have h2 : ⟪y, S.rep (star a) (S.operator x)⟫_ℂ =
      ⟪S.operator ⟨S.rep a y, S.rep_mem_domain a hy⟩, (x : H)⟫_ℂ := by
    rw [hπ_adj, ContinuousLinearMap.adjoint_inner_right,
      ← S.isSelfAdjoint_operator.isFormalAdjoint ⟨S.rep a y, S.rep_mem_domain a hy⟩ x]
  rw [inner_sub_right, h1, h2, neg_apply, inner_neg_right, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ← S.commutator_apply_domain a ⟨y, hy⟩,
    inner_sub_left, neg_sub]

/-- Taking the adjoint preserves the norm of the commutator `[D, π(a)]`. -/
@[simp]
theorem norm_commutator_star (a : A) : ‖S.commutator (star a)‖ = ‖S.commutator a‖ := by
  rw [S.commutator_star, norm_neg, ContinuousLinearMap.star_eq_adjoint,
    LinearIsometryEquiv.norm_map]

/-! #### Graph-norm estimates -/

/-- Pointwise bound on `‖D (π(a) x)‖` in terms of `‖D x‖` and `‖x‖`. -/
theorem norm_operator_rep_le (a : A) (x : S.operator.domain) :
    ‖S.operator ⟨S.rep a x, S.rep_mem_domain a x.property⟩‖ ≤
      ‖S.rep a‖ * ‖S.operator x‖ + ‖S.commutator a‖ * ‖(x : H)‖ := by
  rw [S.operator_rep_apply a x]
  exact (norm_add_le _ _).trans
    (add_le_add ((S.rep a).le_opNorm _) ((S.commutator a).le_opNorm _))

/-- `ℓ¹` graph-norm bound: `π(a)` acts boundedly on `D(D)` with norm at most
`‖π(a)‖ + ‖[D, π(a)]‖`. -/
theorem norm_rep_add_norm_operator_rep_le (a : A) (x : S.operator.domain) :
    ‖S.rep a x‖ + ‖S.operator ⟨S.rep a x, S.rep_mem_domain a x.property⟩‖ ≤
      (‖S.rep a‖ + ‖S.commutator a‖) * (‖(x : H)‖ + ‖S.operator x‖) := by
  have h1 : ‖S.rep a x‖ ≤ ‖S.rep a‖ * ‖(x : H)‖ := (S.rep a).le_opNorm _
  have h2 := S.norm_operator_rep_le a x
  have h3 : 0 ≤ ‖S.commutator a‖ * ‖S.operator x‖ := by positivity
  linarith

/-- Hilbert graph-norm bound:
`‖π(a) x‖² + ‖D (π(a) x)‖² ≤ 2 (‖π(a)‖² + ‖[D, π(a)]‖²) (‖x‖² + ‖D x‖²)`. -/
theorem norm_sq_add_norm_operator_sq_rep_le (a : A) (x : S.operator.domain) :
    ‖S.rep a x‖ ^ 2 + ‖S.operator ⟨S.rep a x, S.rep_mem_domain a x.property⟩‖ ^ 2 ≤
      2 * (‖S.rep a‖ ^ 2 + ‖S.commutator a‖ ^ 2) * (‖(x : H)‖ ^ 2 + ‖S.operator x‖ ^ 2) := by
  have h1sq := pow_le_pow_left₀ (norm_nonneg _) ((S.rep a).le_opNorm (x : H)) 2
  have h2sq := pow_le_pow_left₀ (norm_nonneg _) (S.norm_operator_rep_le a x) 2
  nlinarith [sq_nonneg (‖S.rep a‖ * ‖S.operator x‖ - ‖S.commutator a‖ * ‖(x : H)‖),
    sq_nonneg (‖S.rep a‖ * ‖(x : H)‖), sq_nonneg (‖S.commutator a‖ * ‖S.operator x‖)]

/-! #### Unitary equivalence -/

section Conj

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

private theorem conj_sylvesterEquation (U : H ≃ₗᵢ[ℂ] H') (a : A) :
    LinearPMap.SylvesterEquation (S.operator.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H'))
      (S.operator.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H'))
      (U.conjStarAlgEquiv (S.rep a)) (U.conjStarAlgEquiv (S.commutator a)) where
  mapsTo_domain y :=
    LinearPMap.conjStarAlgEquiv_mem_conj_domain U S.operator (S.rep_mem_domain a) y.property
  equation y := by
    rw [LinearPMap.conj_apply_conjStarAlgEquiv U S.operator (S.rep_mem_domain a) y,
      LinearPMap.conjStarAlgEquiv_apply_conj U S.operator (S.rep a) y, ← map_sub,
      S.commutator_apply_domain a ⟨U.symm y, _⟩, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

/-- **Unitary equivalence.** The spectral triple on `H'` obtained by transporting `S` along the
unitary `U : H ≃ₗᵢ[ℂ] H'`, with representation `U π(a) U*` and Dirac operator `U D U*`. -/
def conj (U : H ≃ₗᵢ[ℂ] H') : SpectralTriple A H' where
  rep := U.conjStarAlgEquiv.toStarAlgHom.comp S.rep
  operator := S.operator.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H')
  isSelfAdjoint_operator := S.isSelfAdjoint_operator.conj U
  hasCompactResolvent_operator :=
    (LinearPMap.hasCompactResolvent_conj_iff (U : H ≃L[ℂ] H')).2 S.hasCompactResolvent_operator
  exists_bounded_commutator a :=
    ⟨U.conjStarAlgEquiv (S.commutator a), S.conj_sylvesterEquation U a⟩

@[simp]
theorem conj_rep_apply (U : H ≃ₗᵢ[ℂ] H') (a : A) :
    (S.conj U).rep a = U.conjStarAlgEquiv (S.rep a) := by rfl

@[simp]
theorem conj_operator (U : H ≃ₗᵢ[ℂ] H') :
    (S.conj U).operator = S.operator.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H') := by rfl

@[simp]
theorem conj_commutator (U : H ≃ₗᵢ[ℂ] H') (a : A) :
    (S.conj U).commutator a = U.conjStarAlgEquiv (S.commutator a) :=
  ((S.conj U).eq_commutator_of_domain (S.conj_sylvesterEquation U a).equation).symm

/-- Transporting back along the inverse unitary recovers the original spectral triple. -/
@[simp]
theorem conj_conj_symm (U : H ≃ₗᵢ[ℂ] H') : (S.conj U).conj U.symm = S := by
  ext1
  · ext1 a; simp [← LinearIsometryEquiv.symm_conjStarAlgEquiv]
  · simp

/-- Transporting along the inverse unitary and then along `U` recovers the original triple. -/
@[simp]
theorem conj_symm_conj (U : H' ≃ₗᵢ[ℂ] H) : (S.conj U.symm).conj U = S := by
  simpa using S.conj_conj_symm U.symm

/-- Transporting along the identity unitary does nothing. -/
@[simp]
theorem conj_refl : S.conj (LinearIsometryEquiv.refl ℂ H) = S := by
  have hrefl : ((LinearIsometryEquiv.refl ℂ H : H ≃L[ℂ] H) : H ≃ₗ[ℂ] H) =
      LinearEquiv.refl ℂ H := LinearEquiv.ext fun _ ↦ rfl
  ext1
  · ext1 a; simp
  · rw [conj_operator, hrefl, LinearPMap.conj_refl]

/-- Transporting along `U` and then along `V` is transporting along their composite. -/
theorem conj_trans {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
    [CompleteSpace H''] (U : H ≃ₗᵢ[ℂ] H') (V : H' ≃ₗᵢ[ℂ] H'') :
    (S.conj U).conj V = S.conj (U.trans V) := by
  ext1
  · ext1 a; ext x; simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  · simp [conj_operator, ← LinearPMap.conj_trans]

end Conj

/-! #### Algebra pullback -/

section Comap

variable {B : Type*} [Semiring B] [Algebra ℂ B] [Star B]

/-- **Algebra pullback.** Restricting the representation of a spectral triple along a unital
`*`-algebra homomorphism `φ : B →⋆ₐ[ℂ] A` yields a spectral triple over `B` with the same Dirac
operator. -/
def comap (φ : B →⋆ₐ[ℂ] A) : SpectralTriple B H where
  rep := S.rep.comp φ
  operator := S.operator
  isSelfAdjoint_operator := S.isSelfAdjoint_operator
  hasCompactResolvent_operator := S.hasCompactResolvent_operator
  exists_bounded_commutator b := S.exists_bounded_commutator (φ b)

@[simp]
theorem comap_rep (φ : B →⋆ₐ[ℂ] A) : (S.comap φ).rep = S.rep.comp φ := by rfl

@[simp]
theorem comap_operator (φ : B →⋆ₐ[ℂ] A) : (S.comap φ).operator = S.operator := by rfl

@[simp]
theorem comap_commutator (φ : B →⋆ₐ[ℂ] A) (b : B) :
    (S.comap φ).commutator b = S.commutator (φ b) :=
  ((S.comap φ).eq_commutator_of_domain fun x ↦ S.commutator_apply_domain (φ b) x).symm

@[simp]
theorem comap_id : S.comap (StarAlgHom.id ℂ A) = S := by
  ext1 <;> first | (ext1 a; rfl) | rfl

theorem comap_comp {C : Type*} [Semiring C] [Algebra ℂ C] [Star C]
    (φ : B →⋆ₐ[ℂ] A) (ψ : C →⋆ₐ[ℂ] B) : (S.comap φ).comap ψ = S.comap (φ.comp ψ) := by rfl

theorem comap_conj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (U : H ≃ₗᵢ[ℂ] H') (φ : B →⋆ₐ[ℂ] A) : (S.conj U).comap φ = (S.comap φ).conj U := by rfl

end Comap

/-! #### Finite-dimensional spectral triples -/

/-- On a finite-dimensional Hilbert space every self-adjoint bounded operator has compact
resolvent and bounded commutators, so every unital `*`-representation and self-adjoint operator
form a spectral triple. -/
def ofFiniteDimensional [FiniteDimensional ℂ H] (π : A →⋆ₐ[ℂ] H →L[ℂ] H) (D : H →L[ℂ] H)
    (hD : IsSelfAdjoint D) : SpectralTriple A H where
  rep := π
  operator := (D : H →ₗ[ℂ] H).toPMap ⊤
  isSelfAdjoint_operator := LinearPMap.isSelfAdjoint_toPMap_top hD
  hasCompactResolvent_operator := hD.hasCompactResolvent_toPMap_top_iff.2 ‹_›
  exists_bounded_commutator a :=
    ⟨D * π a - π a * D, LinearPMap.SylvesterEquation.toPMap_top rfl⟩

@[simp]
theorem ofFiniteDimensional_rep [FiniteDimensional ℂ H] (π : A →⋆ₐ[ℂ] H →L[ℂ] H)
    (D : H →L[ℂ] H) (hD : IsSelfAdjoint D) : (ofFiniteDimensional π D hD).rep = π := by rfl

@[simp]
theorem ofFiniteDimensional_operator [FiniteDimensional ℂ H] (π : A →⋆ₐ[ℂ] H →L[ℂ] H)
    (D : H →L[ℂ] H) (hD : IsSelfAdjoint D) :
    (ofFiniteDimensional π D hD).operator = (D : H →ₗ[ℂ] H).toPMap ⊤ := by rfl

private theorem ofFiniteDimensional_operator_apply [FiniteDimensional ℂ H]
    (π : A →⋆ₐ[ℂ] H →L[ℂ] H) (D : H →L[ℂ] H) (hD : IsSelfAdjoint D)
    (x : (ofFiniteDimensional π D hD).operator.domain) :
    (ofFiniteDimensional π D hD).operator x = D x :=
  ((LinearPMap.ext_iff.mp (ofFiniteDimensional_operator π D hD)).2
      (hf := x.property) (hg := Submodule.mem_top)).trans
    ((LinearMap.toPMap_apply (D : H →ₗ[ℂ] H) ⊤ ⟨x, Submodule.mem_top⟩).trans
      (congrFun (ContinuousLinearMap.coe_coe D) (x : H)))

@[simp]
theorem ofFiniteDimensional_commutator [FiniteDimensional ℂ H] (π : A →⋆ₐ[ℂ] H →L[ℂ] H)
    (D : H →L[ℂ] H) (hD : IsSelfAdjoint D) (a : A) :
    (ofFiniteDimensional π D hD).commutator a = D * π a - π a * D :=
  ((ofFiniteDimensional π D hD).eq_commutator_of_domain fun _ ↦ by
    simp [ofFiniteDimensional_operator_apply, ContinuousLinearMap.mul_def]).symm

end SpectralTriple

/-! ### Even spectral triples -/

namespace EvenSpectralTriple

variable (S : EvenSpectralTriple A H)

/-- The grading of an even spectral triple equals its adjoint. -/
@[simp]
theorem star_grading : star S.grading = S.grading :=
  S.isSelfAdjoint_grading.star_eq

/-- The grading of an even spectral triple anticommutes with every commutator `[D, π(a)]`. -/
theorem grading_mul_commutator (a : A) :
    S.grading * S.commutator a = -(S.commutator a * S.grading) := by
  ext x
  refine congrFun (Continuous.ext_on S.dense_domain
    (S.grading * S.commutator a).continuous (-(S.commutator a * S.grading)).continuous
    fun y hy ↦ ?_) x
  have hcomm (z : H) : S.grading (S.rep a z) = S.rep a (S.grading z) := by
    simpa [ContinuousLinearMap.mul_def] using
      congrArg (fun T : H →L[ℂ] H ↦ T z) (S.commute_grading_rep a).eq
  have hmem : (⟨S.grading (S.rep a y), S.grading_mem_domain (S.rep_mem_domain a hy)⟩ :
      S.operator.domain) = ⟨S.rep a (S.grading y), S.rep_mem_domain a (S.grading_mem_domain hy)⟩ :=
    Subtype.ext (hcomm y)
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, neg_apply]
  rw [← S.commutator_apply_domain a ⟨y, hy⟩,
    ← S.commutator_apply_domain a ⟨S.grading y, S.grading_mem_domain hy⟩,
    map_sub, S.grading_apply_operator ⟨S.rep a y, S.rep_mem_domain a hy⟩, hmem,
    hcomm (S.operator ⟨y, hy⟩), S.grading_apply_operator ⟨y, hy⟩, map_neg]
  abel

section Conj

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

private theorem conj_grading_apply_operator (U : H ≃ₗᵢ[ℂ] H')
    (y : (S.operator.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H')).domain) :
    (U.conjStarAlgEquiv S.grading) (S.operator.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H') y) =
      -(S.operator.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H')
        ⟨U.conjStarAlgEquiv S.grading y,
          LinearPMap.conjStarAlgEquiv_mem_conj_domain U S.operator S.grading_mem_domain
            y.property⟩) := by
  rw [LinearPMap.conjStarAlgEquiv_apply_conj, LinearPMap.conj_apply_conjStarAlgEquiv,
    S.grading_apply_operator, map_neg]

/-- **Unitary equivalence**, even version: the grading is transported to `U γ U*`. -/
def conj (U : H ≃ₗᵢ[ℂ] H') : EvenSpectralTriple A H' where
  toSpectralTriple := S.toSpectralTriple.conj U
  grading := U.conjStarAlgEquiv S.grading
  isSelfAdjoint_grading := S.isSelfAdjoint_grading.map U.conjStarAlgEquiv
  grading_mul_grading := by rw [← map_mul, S.grading_mul_grading, map_one]
  commute_grading_rep a := by
    rw [SpectralTriple.conj_rep_apply]
    exact (S.commute_grading_rep a).map U.conjStarAlgEquiv
  grading_mem_domain hy :=
    LinearPMap.conjStarAlgEquiv_mem_conj_domain U S.operator S.grading_mem_domain hy
  grading_apply_operator := S.conj_grading_apply_operator U

@[simp]
theorem conj_toSpectralTriple (U : H ≃ₗᵢ[ℂ] H') :
    (S.conj U).toSpectralTriple = S.toSpectralTriple.conj U := by rfl

@[simp]
theorem conj_grading (U : H ≃ₗᵢ[ℂ] H') :
    (S.conj U).grading = U.conjStarAlgEquiv S.grading := by rfl

/-- Transporting back along the inverse unitary recovers the original even spectral triple. -/
@[simp]
theorem conj_conj_symm (U : H ≃ₗᵢ[ℂ] H') : (S.conj U).conj U.symm = S := by
  ext1
  · ext1 a; simp
  · simp
  · simp [← LinearIsometryEquiv.symm_conjStarAlgEquiv]

/-- Transporting along the inverse unitary and then along `U` recovers the original triple. -/
@[simp]
theorem conj_symm_conj (U : H' ≃ₗᵢ[ℂ] H) : (S.conj U.symm).conj U = S := by
  simpa using S.conj_conj_symm U.symm

/-- Transporting along the identity unitary does nothing. -/
@[simp]
theorem conj_refl : S.conj (LinearIsometryEquiv.refl ℂ H) = S := by
  ext1
  · ext1 a; simp
  · simp
  · simp

/-- Transporting along `U` and then along `V` is transporting along their composite. -/
theorem conj_trans {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
    [CompleteSpace H''] (U : H ≃ₗᵢ[ℂ] H') (V : H' ≃ₗᵢ[ℂ] H'') :
    (S.conj U).conj V = S.conj (U.trans V) := by
  ext1
  · ext1 a; ext x; simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  · simp [SpectralTriple.conj_operator, ← LinearPMap.conj_trans]
  · ext x; simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

end Conj

section Comap

variable {B : Type*} [Semiring B] [Algebra ℂ B] [Star B]

/-- **Algebra pullback**, even version: restricts the representation along `φ : B →⋆ₐ[ℂ] A` while
keeping the Dirac operator and grading unchanged. -/
def comap (φ : B →⋆ₐ[ℂ] A) : EvenSpectralTriple B H where
  toSpectralTriple := S.toSpectralTriple.comap φ
  grading := S.grading
  isSelfAdjoint_grading := S.isSelfAdjoint_grading
  grading_mul_grading := S.grading_mul_grading
  commute_grading_rep b := S.commute_grading_rep (φ b)
  grading_mem_domain hx := S.grading_mem_domain hx
  grading_apply_operator x := S.grading_apply_operator x

@[simp]
theorem comap_toSpectralTriple (φ : B →⋆ₐ[ℂ] A) :
    (S.comap φ).toSpectralTriple = S.toSpectralTriple.comap φ := by rfl

@[simp]
theorem comap_grading (φ : B →⋆ₐ[ℂ] A) : (S.comap φ).grading = S.grading := by rfl

@[simp]
theorem comap_id : S.comap (StarAlgHom.id ℂ A) = S := by
  ext1 <;> first | (ext1 a; rfl) | rfl

theorem comap_comp {C : Type*} [Semiring C] [Algebra ℂ C] [Star C]
    (φ : B →⋆ₐ[ℂ] A) (ψ : C →⋆ₐ[ℂ] B) : (S.comap φ).comap ψ = S.comap (φ.comp ψ) := by rfl

theorem comap_conj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (U : H ≃ₗᵢ[ℂ] H') (φ : B →⋆ₐ[ℂ] A) : (S.conj U).comap φ = (S.comap φ).conj U := by rfl

end Comap

/-- On a finite-dimensional Hilbert space, every unital `*`-representation, self-adjoint operator
`D`, and grading `γ` commuting with the representation and anticommuting with `D` form an even
spectral triple. -/
def ofFiniteDimensional [FiniteDimensional ℂ H] (π : A →⋆ₐ[ℂ] H →L[ℂ] H) (D : H →L[ℂ] H)
    (hD : IsSelfAdjoint D) (γ : H →L[ℂ] H) (hγ : IsSelfAdjoint γ) (hγγ : γ * γ = 1)
    (hγπ : ∀ a, Commute γ (π a)) (hγD : γ * D = -(D * γ)) : EvenSpectralTriple A H where
  toSpectralTriple := SpectralTriple.ofFiniteDimensional π D hD
  grading := γ
  isSelfAdjoint_grading := hγ
  grading_mul_grading := hγγ
  commute_grading_rep := hγπ
  grading_mem_domain _ := Submodule.mem_top
  grading_apply_operator x := by
    rw [SpectralTriple.ofFiniteDimensional_operator_apply,
      SpectralTriple.ofFiniteDimensional_operator_apply]
    simpa [ContinuousLinearMap.mul_def] using congrArg (fun T : H →L[ℂ] H ↦ T (x : H)) hγD

@[simp]
theorem ofFiniteDimensional_toSpectralTriple [FiniteDimensional ℂ H] (π : A →⋆ₐ[ℂ] H →L[ℂ] H)
    (D : H →L[ℂ] H) (hD) (γ : H →L[ℂ] H) (hγ hγγ hγπ hγD) :
    (ofFiniteDimensional π D hD γ hγ hγγ hγπ hγD).toSpectralTriple =
      SpectralTriple.ofFiniteDimensional π D hD := by rfl

@[simp]
theorem ofFiniteDimensional_grading [FiniteDimensional ℂ H] (π : A →⋆ₐ[ℂ] H →L[ℂ] H)
    (D : H →L[ℂ] H) (hD) (γ : H →L[ℂ] H) (hγ hγγ hγπ hγD) :
    (ofFiniteDimensional π D hD γ hγ hγγ hγπ hγD).grading = γ := by rfl

end EvenSpectralTriple

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTwist
public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.Symmetric.Specht.Character
public import TauCeti.RepresentationTheory.Symmetric.Specht.Comparison
public import TauCeti.RepresentationTheory.Symmetric.Specht.Ideal.Idempotent
public import TauCeti.RepresentationTheory.Symmetric.Transpose

/-!
# The Specht module of the conjugate partition

Tensoring a Specht module with the sign representation gives the Specht module of the conjugate
partition: `S^μ ⊗ sgn ≅ S^(μᵗ)`.  This is the representation-level form of the row/column symmetry
of Young diagrams, and its trace is the character identity `χ^(μᵗ)(σ) = sgn(σ) χ^μ(σ)`.

The isomorphism comes from an explicit map between the Young-symmetrizer left ideals.  Let
`ψ = TauCeti.YoungTableau.signTransposeAlgEquiv μ` be the sign-transpose isomorphism of group
algebras, so that `ψ(a_t) = b_(tᵗ)` and `ψ(b_t) = a_(tᵗ)`.  Then

`F_t : ℚ[Sₙ] c_t → ℚ[Sₙ] c_(tᵗ)`, `F_t(x) = ψ(x) b_(tᵗ)`

is well defined: `ψ(y c_t) b_(tᵗ) = ψ(y) b_(tᵗ) a_(tᵗ) b_(tᵗ)`.  The right factor `b_(tᵗ)` matters,
since `ψ(y c_t)` itself lies in the opposite-order ideal `ℚ[Sₙ] b_(tᵗ) a_(tᵗ)`.  The map `F_t` is
`ψ`-semilinear, so it intertwines the action on the source twisted by the sign with the action on
the target.

`F_t` is not an involution: `F_(tᵗ) (F_t x) = ψ(ψ(x)) c_(tᵗᵗ) = κ_t ψ(ψ(x))`, where `ψ ∘ ψ` is the
relabelling from `μ` to `μᵗᵗ` and `κ_t = n! / dim ℚ[Sₙ] c_t` is the scalar of the essential
idempotence `c_t c_t = κ_t c_t`.  Already for `μ = (2)` this scalar is `2`.  It is nonzero, so `F_t`
is nonzero, and Schur's lemma makes it bijective.

## Main definitions

* `TauCeti.YoungTableau.spechtIdealSignTranspose`: the intertwiner `F_t`.
* `TauCeti.YoungTableau.spechtIdealSignTransposeEquiv`: `F_t` as an equivalence of representations.
* `TauCeti.YoungTableau.spechtSubrepresentationTensorSignEquiv`: the resulting equivalence
  `S^μ ⊗ sgn ≃ S^(μᵗ)` between the polytabloid Specht modules of the diagrams `μ` and `μᵗ`.

## Main results

* `TauCeti.YoungTableau.spechtIdealSignTranspose_transpose_apply_coe`: the composite
  `F_(tᵗ) ∘ F_t` is `κ_t` times the relabelling.
* `TauCeti.YoungTableau.coe_spechtIdealSignTransposeEquiv_symm_apply`: the inverse of `F_t` is
  `κ_t⁻¹ F_(tᵗ)` after the relabelling.
* `TauCeti.YoungTableau.spechtIdealSignTranspose_relabelEquiv_apply_coe`: changing the tableau
  changes `F_t` by the sign of the relabelling.
* `TauCeti.YoungTableau.factorial_div_finrank_spechtIdeal_transpose`: `κ_(tᵗ) = κ_t`.
* `TauCeti.spechtModule_tensor_sign_iso`: **`S^μ ⊗ sgn ≅ S^(μᵗ)`** in
  `FDRep ℚ (Equiv.Perm (Fin n))`.
* `TauCeti.spechtChar_conjugate`: **`χ^(μᵗ)(σ) = sgn(σ) χ^μ(σ)`**.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 4, Exercise 4.4.
* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Theorem 8.15.
-/

public section

open CategoryTheory MonoidalCategory Module
open scoped TensorProduct

namespace TauCeti

namespace YoungTableau

variable {μ : YoungDiagram}

noncomputable section

/-- `ψ(x) b_(tᵗ)` lies in the left ideal of `c_(tᵗ)` for `x` in the left ideal of `c_t`. -/
private theorem signTransposeAlgEquiv_mul_columnAntisymmetrizer_mem {t : YoungTableau μ}
    {x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))} (hx : x ∈ spechtIdeal t) :
    signTransposeAlgEquiv ℚ μ x * columnAntisymmetrizer (transpose t) ∈
      spechtIdeal (transpose t) := by
  obtain ⟨a, rfl⟩ := (mem_spechtIdeal_iff t x).mp hx
  rw [mem_spechtIdeal_iff]
  refine ⟨signTransposeAlgEquiv ℚ μ a * columnAntisymmetrizer (transpose t), ?_⟩
  rw [map_mul, signTransposeAlgEquiv_youngSymmetrizer, youngSymmetrizer_def]
  simp only [mul_assoc]

/-- The underlying linear map `x ↦ ψ(x) b_(tᵗ)` of the sign-transpose intertwiner. -/
private def spechtIdealSignTransposeLinearMap (t : YoungTableau μ) :
    spechtIdeal t →ₗ[ℚ] spechtIdeal (transpose t) where
  toFun x :=
    ⟨signTransposeAlgEquiv ℚ μ (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) *
        columnAntisymmetrizer (transpose t),
      signTransposeAlgEquiv_mul_columnAntisymmetrizer_mem x.property⟩
  map_add' x y := Subtype.ext <| by
    simp only [Submodule.coe_add, map_add, add_mul]
  map_smul' r x := Subtype.ext <| by
    simp only [Submodule.coe_smul_of_tower, map_smul, smul_mul_assoc, RingHom.id_apply]

private theorem coe_spechtIdealSignTransposeLinearMap_apply (t : YoungTableau μ)
    (x : spechtIdeal t) :
    (spechtIdealSignTransposeLinearMap t x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.transpose.card))) =
      signTransposeAlgEquiv ℚ μ (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) *
        columnAntisymmetrizer (transpose t) :=
  rfl

/-- The **sign-transpose intertwiner** `F_t : ℚ[Sₙ] c_t → ℚ[Sₙ] c_(tᵗ)`, `x ↦ ψ(x) b_(tᵗ)`.  It
intertwines the action on `ℚ[Sₙ] c_t` twisted by the sign with the action on `ℚ[Sₙ] c_(tᵗ)`, the
symmetric groups on the labels of `μ` and of `μᵗ` being identified.  It is not the bare `ψ`, which
lands in the opposite-order ideal `ℚ[Sₙ] b_(tᵗ) a_(tᵗ)`. -/
def spechtIdealSignTranspose (t : YoungTableau μ) :
    (Representation.charTwist (signLinearCharacter ℚ (Fin μ.card))
        (spechtIdealRep t).ρ).IntertwiningMap
      ((spechtIdealRep (transpose t)).ρ.comp
        (finCongr (YoungDiagram.card_transpose μ).symm).permCongrHom.toMonoidHom) where
  toLinearMap := spechtIdealSignTransposeLinearMap t
  isIntertwining' g := LinearMap.ext fun x => Subtype.ext <| by
    -- Unpack the two actions into products in the group algebras.
    rw [LinearMap.comp_apply, LinearMap.comp_apply, MonoidHom.comp_apply,
      Representation.charTwist_apply_apply, MulEquiv.coe_toMonoidHom, map_smul,
      spechtIdealRep_ρ_apply_coe, coe_spechtIdealSignTransposeLinearMap_apply,
      Submodule.coe_smul_of_tower, coe_spechtIdealSignTransposeLinearMap_apply,
      spechtIdealRep_ρ_apply_coe, coe_signLinearCharacter_apply]
    -- `ψ(g x) = ψ(g) ψ(x)` and `sgn(g) ψ(g)` is the group element `g` read on the labels of `μᵗ`.
    rw [map_mul, ← signTransposeAlgEquiv_sign_smul_single, map_smul]
    simp only [smul_mul_assoc, mul_assoc]

/-- The sign-transpose intertwiner is `x ↦ ψ(x) b_(tᵗ)`. -/
@[simp]
theorem coe_spechtIdealSignTranspose_apply (t : YoungTableau μ) (x : spechtIdeal t) :
    ((spechtIdealSignTranspose t x : spechtIdeal (transpose t)) :
      MonoidAlgebra ℚ (Equiv.Perm (Fin μ.transpose.card))) =
      signTransposeAlgEquiv ℚ μ (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) *
        columnAntisymmetrizer (transpose t) :=
  (rfl)

/-- **The composite `F_(tᵗ) ∘ F_t` is `κ_t` times the relabelling**, for
`κ_t = n! / dim ℚ[Sₙ] c_t`: the two signs cancel and the factors `a_(tᵗᵗ) b_(tᵗᵗ)` left behind are
`c_(tᵗᵗ)`, which is `c_t` relabelled.  In particular `F_t` is not an involution in general. -/
theorem spechtIdealSignTranspose_transpose_apply_coe (t : YoungTableau μ) (x : spechtIdeal t) :
    ((spechtIdealSignTranspose (transpose t) (spechtIdealSignTranspose t x) :
        spechtIdeal (transpose (transpose t))) :
      MonoidAlgebra ℚ (Equiv.Perm (Fin μ.transpose.transpose.card))) =
      ((μ.card.factorial : ℚ) / (finrank ℚ (spechtIdeal t) : ℚ)) •
        MonoidAlgebra.domCongr ℚ ℚ
          (finCongr ((YoungDiagram.card_transpose μ).symm.trans
            (YoungDiagram.card_transpose μ.transpose).symm)).permCongrHom
          (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) := by
  rw [← map_smul, ← mul_youngSymmetrizer_of_mem_spechtIdeal x.property, map_mul,
    ← signTransposeAlgEquiv_transpose_apply, ← signTransposeAlgEquiv_transpose_apply,
    coe_spechtIdealSignTranspose_apply, coe_spechtIdealSignTranspose_apply]
  simp [mul_assoc]

/-- The scalar `κ_t = n! / dim ℚ[Sₙ] c_t` is nonzero. -/
private theorem factorial_div_finrank_spechtIdeal_ne_zero (t : YoungTableau μ) :
    (μ.card.factorial : ℚ) / (finrank ℚ (spechtIdeal t) : ℚ) ≠ 0 :=
  div_ne_zero (Nat.cast_ne_zero.mpr μ.card.factorial_ne_zero)
    (Nat.cast_ne_zero.mpr (finrank_spechtIdeal_pos t).ne')

/-- The sign-transpose intertwiner is nonzero: `F_(tᵗ) (F_t c_t)` is a nonzero multiple of the
nonzero element `c_t`, relabelled. -/
theorem spechtIdealSignTranspose_ne_zero (t : YoungTableau μ) : spechtIdealSignTranspose t ≠ 0 := by
  intro h
  have hc := spechtIdealSignTranspose_transpose_apply_coe t
    ⟨youngSymmetrizer (R := ℚ) t, youngSymmetrizer_mem_spechtIdeal t⟩
  have h0 : spechtIdealSignTranspose t
      ⟨youngSymmetrizer (R := ℚ) t, youngSymmetrizer_mem_spechtIdeal t⟩ = 0 := by
    rw [h, Representation.IntertwiningMap.coe_zero, Pi.zero_apply]
  rw [h0, map_zero, Submodule.coe_zero, eq_comm, smul_eq_zero, EmbeddingLike.map_eq_zero_iff] at hc
  exact youngSymmetrizer_ne_zero t (hc.resolve_left (factorial_div_finrank_spechtIdeal_ne_zero t))

/-- **The sign-transpose intertwiner is an equivalence of representations**, by Schur's lemma: it
is a nonzero map between irreducible representations. -/
def spechtIdealSignTransposeEquiv (t : YoungTableau μ) :
    (Representation.charTwist (signLinearCharacter ℚ (Fin μ.card)) (spechtIdealRep t).ρ).Equiv
      ((spechtIdealRep (transpose t)).ρ.comp
        (finCongr (YoungDiagram.card_transpose μ).symm).permCongrHom.toMonoidHom) :=
  haveI : Representation.IsIrreducible ((spechtIdealRep (transpose t)).ρ.comp
      (finCongr (YoungDiagram.card_transpose μ).symm).permCongrHom.toMonoidHom) :=
    (MulEquiv.isIrreducible_comp_equiv_iff
      (finCongr (YoungDiagram.card_transpose μ).symm).permCongrHom
      (spechtIdealRep (transpose t)).ρ).mpr inferInstance
  (spechtIdealSignTranspose t).ofBijective
    ((Representation.IsIrreducible.bijective_or_eq_zero
      (spechtIdealSignTranspose t)).resolve_right (spechtIdealSignTranspose_ne_zero t))

/-- The equivalence `F_t` is the sign-transpose intertwiner on elements. -/
@[simp]
theorem spechtIdealSignTransposeEquiv_apply (t : YoungTableau μ) (x : spechtIdeal t) :
    spechtIdealSignTransposeEquiv t x = spechtIdealSignTranspose t x :=
  (rfl)

/-- **The inverse of `F_t` is `κ_t⁻¹ F_(tᵗ)` after the relabelling** from `μᵗᵗ` back to `μ`. -/
theorem coe_spechtIdealSignTransposeEquiv_symm_apply (t : YoungTableau μ)
    (y : spechtIdeal (transpose t)) :
    (((spechtIdealSignTransposeEquiv t).symm y : spechtIdeal t) :
      MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) =
      ((μ.card.factorial : ℚ) / (finrank ℚ (spechtIdeal t) : ℚ))⁻¹ •
        (MonoidAlgebra.domCongr ℚ ℚ
          (finCongr ((YoungDiagram.card_transpose μ).symm.trans
            (YoungDiagram.card_transpose μ.transpose).symm)).permCongrHom).symm
          ((spechtIdealSignTranspose (transpose t) y : spechtIdeal (transpose (transpose t))) :
            MonoidAlgebra ℚ (Equiv.Perm (Fin μ.transpose.transpose.card))) := by
  have hy : spechtIdealSignTranspose t ((spechtIdealSignTransposeEquiv t).symm y) = y :=
    (spechtIdealSignTransposeEquiv t).apply_symm_apply y
  rw [eq_inv_smul_iff₀ (factorial_div_finrank_spechtIdeal_ne_zero t), AlgEquiv.eq_symm_apply,
    map_smul, ← spechtIdealSignTranspose_transpose_apply_coe, hy]

/-- **The sign-transpose intertwiners of `t` and of a relabelling `σt` differ by the sign of `σ`**,
through the native relabelling isomorphisms `x ↦ x σ` of the left ideals on either side:
`F_t(x σ) = sgn(σ) F_(σt)(x) σ`. -/
theorem spechtIdealSignTranspose_relabelEquiv_apply_coe (σ : Equiv.Perm (Fin μ.card))
    (t : YoungTableau μ) (x : spechtIdeal (relabel σ t)) :
    ((spechtIdealSignTranspose t (spechtIdealRelabelEquiv σ t x) : spechtIdeal (transpose t)) :
      MonoidAlgebra ℚ (Equiv.Perm (Fin μ.transpose.card))) =
      ((Equiv.Perm.sign σ : ℤ) : ℚ) •
        (((spechtIdealSignTranspose (relabel σ t) x : spechtIdeal (transpose (relabel σ t))) :
          MonoidAlgebra ℚ (Equiv.Perm (Fin μ.transpose.card))) *
            MonoidAlgebra.single ((finCongr (YoungDiagram.card_transpose μ).symm).permCongrHom σ)
              1) := by
  have hunit (τ : Equiv.Perm (Fin μ.transpose.card)) :
      MonoidAlgebra.single τ⁻¹ (1 : ℚ) * MonoidAlgebra.single τ 1 = 1 := by
    rw [MonoidAlgebra.single_mul_single, inv_mul_cancel, mul_one, MonoidAlgebra.one_def]
  have hsign (τ : Equiv.Perm (Fin μ.transpose.card)) (r : ℚ) :
      MonoidAlgebra.single τ (r * 1) = r • MonoidAlgebra.single τ 1 := by
    rw [MonoidAlgebra.smul_single, smul_eq_mul]
  rw [coe_spechtIdealSignTranspose_apply, coe_spechtIdealSignTranspose_apply,
    spechtIdealRelabelEquiv_apply_coe, transpose_relabel, columnAntisymmetrizer_relabel, map_mul,
    signTransposeAlgEquiv_single, hsign, Equiv.permCongrHom_coe]
  simp only [mul_assoc, hunit, mul_one, mul_smul_comm, smul_mul_assoc]

/-- The left ideals of `c_t` and of `c_(tᵗ)` have the same dimension. -/
theorem finrank_spechtIdeal_transpose (t : YoungTableau μ) :
    finrank ℚ (spechtIdeal (transpose t)) = finrank ℚ (spechtIdeal t) :=
  (spechtIdealSignTransposeEquiv t).toLinearEquiv.finrank_eq.symm

/-- **The scalars of essential idempotence of `t` and of `tᵗ` agree**: `κ_(tᵗ) = κ_t`. -/
theorem factorial_div_finrank_spechtIdeal_transpose (t : YoungTableau μ) :
    (μ.transpose.card.factorial : ℚ) / (finrank ℚ (spechtIdeal (transpose t)) : ℚ) =
      (μ.card.factorial : ℚ) / (finrank ℚ (spechtIdeal t) : ℚ) := by
  rw [finrank_spechtIdeal_transpose, YoungDiagram.card_transpose]

/-- **The polytabloid Specht modules of `μ` and `μᵗ` are exchanged by the sign**: tensoring
`S^μ` with the sign representation gives `S^(μᵗ)`, the symmetric groups on the labels of `μ` and of
`μᵗ` being identified.  The tableau `t` chooses the map: it is `F_t` read through the comparison of
each Specht module with its Young-symmetrizer ideal. -/
def spechtSubrepresentationTensorSignEquiv (t : YoungTableau μ) :
    ((spechtSubrepresentation (R := ℚ) μ).toRepresentation.tprod
        (Representation.ofLinearCharacter (signLinearCharacter ℚ (Fin μ.card)))).Equiv
      ((spechtSubrepresentation (R := ℚ) μ.transpose).toRepresentation.comp
        (finCongr (YoungDiagram.card_transpose μ).symm).permCongrHom.toMonoidHom) :=
  (((spechtIdealEquivSpechtSubrepresentation t).symm.tprod (.refl _)).trans
    (Representation.tprodOfLinearCharacterEquivCharTwist _ _)).trans
      ((spechtIdealSignTransposeEquiv t).trans
        ((spechtIdealEquivSpechtSubrepresentation (transpose t)).res _))

/-- On a pure tensor, the equivalence `S^μ ⊗ sgn ≃ S^(μᵗ)` chosen by `t` is `F_t` read through the
comparisons of the two Specht modules with their Young-symmetrizer ideals. -/
theorem spechtSubrepresentationTensorSignEquiv_tmul (t : YoungTableau μ)
    (v : (spechtSubrepresentation (R := ℚ) μ).toSubmodule) (r : ℚ) :
    spechtSubrepresentationTensorSignEquiv t (v ⊗ₜ[ℚ] r) =
      r • spechtIdealEquivSpechtSubrepresentation (transpose t)
        (spechtIdealSignTranspose t ((spechtIdealEquivSpechtSubrepresentation t).symm v)) := by
  simp only [spechtSubrepresentationTensorSignEquiv, Representation.Equiv.trans_apply,
    Representation.Equiv.tprod_tmul, Representation.Equiv.refl_apply,
    Representation.tprodOfLinearCharacterEquivCharTwist_tmul, map_smul,
    Representation.Equiv.res_apply]
  -- this is `spechtIdealSignTransposeEquiv_apply`, which `simp` does not match since it reads the
  -- source carrier as `spechtIdealRep t` rather than `spechtIdeal t`
  rfl

end

end YoungTableau

section Partition

variable {n : ℕ}

/-- `S^μ ⊗ sgn ≃ S^(μᵗ)` with the two diagrams of `n` cells given separately, which is what lets
the identification of the diagram of `μᵗ` with the transpose of the diagram of `μ` be eliminated. -/
private theorem nonempty_equiv_tprod_sign {D E : YoungDiagram} (hD : n = D.card) (hE : n = E.card)
    (h : E = D.transpose) :
    Nonempty ((Representation.tprod
        ((spechtSubrepresentation (R := ℚ) D).toRepresentation.comp
          (finCongr hD).permCongrHom.toMonoidHom)
        (Representation.ofLinearCharacter (signLinearCharacter ℚ (Fin n)))).Equiv
      ((spechtSubrepresentation (R := ℚ) E).toRepresentation.comp
        (finCongr hE).permCongrHom.toMonoidHom)) := by
  subst h
  obtain ⟨t⟩ := YoungTableau.nonempty D
  have hsource : Representation.tprod
      ((spechtSubrepresentation (R := ℚ) D).toRepresentation.comp
        (finCongr hD).permCongrHom.toMonoidHom)
      (Representation.ofLinearCharacter (signLinearCharacter ℚ (Fin n))) =
      ((spechtSubrepresentation (R := ℚ) D).toRepresentation.tprod
        (Representation.ofLinearCharacter (signLinearCharacter ℚ (Fin D.card)))).comp
        (finCongr hD).permCongrHom.toMonoidHom := by
    rw [← signLinearCharacter_comp_permCongrHom (finCongr hD),
      ← Representation.ofLinearCharacter_comp]
    -- the action on a tensor product is computed pointwise in the group
    rfl
  have htarget : (finCongr hE).permCongrHom.toMonoidHom =
      (finCongr (YoungDiagram.card_transpose D).symm).permCongrHom.toMonoidHom.comp
        (finCongr hD).permCongrHom.toMonoidHom := by
    ext σ x
    simp [Equiv.permCongr_apply]
  rw [hsource, htarget, ← MonoidHom.comp_assoc]
  exact ⟨(YoungTableau.spechtSubrepresentationTensorSignEquiv t).res _⟩

/-- **The Specht module of the conjugate partition is the sign twist**: `S^μ ⊗ sgn_n ≅ S^(μᵗ)` in
`FDRep ℚ (Equiv.Perm (Fin n))`. -/
theorem spechtModule_tensor_sign_iso (μ : n.Partition) :
    Nonempty (spechtModule (R := ℚ) μ ⊗ FDRep.ofLinearCharacter (signLinearCharacter ℚ (Fin n)) ≅
      spechtModule (R := ℚ) μ.conjugate) := by
  obtain ⟨e⟩ := nonempty_equiv_tprod_sign (n := n) (D := YoungDiagram.ofPartition μ)
    (E := YoungDiagram.ofPartition μ.conjugate) (YoungDiagram.card_ofPartition μ).symm
    (YoungDiagram.card_ofPartition μ.conjugate).symm (YoungDiagram.ofPartition_conjugate μ)
  rw [FDRep.ofLinearCharacter_def]
  exact ⟨LinearEquiv.toFDRepIso e.toLinearEquiv fun g x =>
    DFunLike.congr_fun (e.toIntertwiningMap.isIntertwining' g) x⟩

/-- **The character of the Specht module of the conjugate partition**:
`χ^(μᵗ)(σ) = sgn(σ) χ^μ(σ)`. -/
theorem spechtChar_conjugate (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    spechtChar μ.conjugate σ = (Equiv.Perm.sign σ : ℤ) * spechtChar μ σ := by
  obtain ⟨e⟩ := spechtModule_tensor_sign_iso μ
  have h := congrFun (FDRep.char_iso e) σ
  rw [FDRep.char_tensor, Pi.mul_apply, FDRep.char_ofLinearCharacter,
    coe_signLinearCharacter_apply] at h
  rw [← Int.cast_inj (α := ℚ), Int.cast_mul, spechtChar_cast, spechtChar_cast, ← h, mul_comm]

end Partition

end TauCeti

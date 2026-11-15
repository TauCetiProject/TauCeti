/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Basic
public import TauCeti.RepresentationTheory.Symmetric.Specht.Decomposition

-- Non-public: `TauCeti.DirectSum.restrictSubtypeLinearEquiv` drops the zero summands inside the
-- construction of `TauCeti.schurWeylDecomposition`; no statement here mentions it.
import TauCeti.Algebra.DirectSum.FiniteSupport

/-!
# The Schur-Weyl decomposition of a tensor power

The symmetric group `S_d` and the general linear group `GL n k` act on the tensor power `(kⁿ)^{⊗d}`
with commuting actions (`TauCeti.permTensorPowerRep`). Over a field `k` of characteristic zero,
Schur-Weyl duality decomposes it under the product group as

`⨁_{μ ⊢ d} S^μ ⊗ 𝕊^μ(kⁿ) ≅ (kⁿ)^{⊗d}`,

where `S^μ` is the Specht module of `μ`, here in its ideal presentation `k[S_d] c_μ`, and
`𝕊^μ(kⁿ)` is the Weyl module of the shape of `μ` (`TauCeti.weylModuleOfShape`), the image of a
Young symmetrizer in `(kⁿ)^{⊗|μ|}`. This is `TauCeti.schurWeylEquiv`, an equivalence of
representations of `S_d × GL n k`; the summand `a ⊗ w` goes to `a · w`, with `w` read in
`(kⁿ)^{⊗d}` by relabeling its tensor factors.

Two inputs are combined. The decomposition `⨁_μ k[S_d] c_μ ⊗ c_μ M ≅ M` of any finite-dimensional
representation of `S_d` (`Representation.youngSymmetrizerEquiv`) applies to `M = (kⁿ)^{⊗d}`, and is
`GL n k`-equivariant because `GL n k` commutes with `k[S_d]` and so acts on each image `c_μ M`.
That image is the Weyl module of the shape of `μ`, once the labels `Fin |μ|` of the diagram are
identified with `Fin d` (`TauCeti.map_reindex_weylModuleOfShape`), and relabeling the tensor factors
is an equivalence of representations of `GL n k` (`TauCeti.weylRepOfShapeEquivRange`).

The Weyl modules here are already known to be irreducible when nonzero
(`TauCeti.isIrreducible_weylRepOfShape_iff`), to vanish exactly for the shapes with more than `n`
rows, and to have the Schur polynomials as characters, so the decomposition exhibits each
irreducible polynomial representation `𝕊^μ(kⁿ)` with multiplicity `dim S^μ`.

Over `ℂ` the decomposition is restated with the named objects: the left factors become the complex
Specht modules `S^μ_ℂ` (`TauCeti.spechtModuleℂ`), through the identification
`Nat.Partition.spanYoungSymmetrizerEquivSpechtModuleℂ` of `ℂ[S_d] c_μ` with `S^μ_ℂ`, the right
factors are the Schur functors `𝕊^μ(ℂⁿ)` (`TauCeti.schurFunctor`), and the summands of the
partitions with more than `n` parts, whose Schur functors vanish, are dropped. This is
`TauCeti.schurWeylDecomposition`,

`(ℂⁿ)^{⊗d} ≅ ⨁_{μ ⊢ d, ℓ(μ) ≤ n} S^μ_ℂ ⊗ 𝕊^μ(ℂⁿ)`,

an equivalence of representations of `S_d × GL n ℂ`, indexed by the subtype
`{μ : d.Partition // μ.parts.card ≤ n}`; the two equivariances are also stated separately, against
`TauCeti.permTensorAction` and `TauCeti.tensorPowerRep`.

## Main definitions

* `TauCeti.weylRepOfShapeEquivRange`: the Weyl module of the shape of `μ` is the image of the Young
  symmetrizer `c_μ` in `(kⁿ)^{⊗d}`, as representations of `GL n k`.
* `TauCeti.schurWeylEquiv`: **the Schur-Weyl decomposition**
  `⨁_μ k[S_d] c_μ ⊗ 𝕊^μ(kⁿ) ≅ (kⁿ)^{⊗d}` of representations of `S_d × GL n k`.
* `TauCeti.schurWeylDecomposition`: **the complex Schur-Weyl decomposition**
  `(ℂⁿ)^{⊗d} ≅ ⨁_{μ ⊢ d, ℓ(μ) ≤ n} S^μ_ℂ ⊗ 𝕊^μ(ℂⁿ)` of representations of `S_d × GL n ℂ`.

## Main results

* `TauCeti.map_reindex_weylModuleOfShape`: relabeling the tensor factors carries the Weyl module of
  the shape of `μ` onto `c_μ (kⁿ)^{⊗d}`.
* `TauCeti.schurWeylDecomposition_comp_permTensorAction` and
  `TauCeti.schurWeylDecomposition_comp_tensorPowerRep`: the complex decomposition intertwines the
  permutation of the tensor factors with the Specht actions, and the diagonal action of `GL n ℂ`
  with the Schur-functor actions.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 6, Theorem 6.3
  and §6.1.
* C. Procesi, *Lie Groups: An Approach through Invariants and Representations* (2007), Chapter 9.
-/

public section

open Module
open scoped DirectSum TensorProduct

namespace TauCeti

variable (k : Type*) (n d : ℕ)

section CommRing

variable [CommRing k] [Algebra ℚ k]

/-- **The Weyl module of the shape of `μ` is the image of the Young symmetrizer `c_μ`**, after
relabeling the tensor factors of `(kⁿ)^{⊗|μ|}` along `YoungDiagram.card_ofPartition`. -/
theorem map_reindex_weylModuleOfShape (μ : d.Partition) :
    (weylModuleOfShape k n (YoungDiagram.ofPartition μ)).toSubmodule.map
        (PiTensorProduct.reindex k (fun _ => Fin n → k)
          (finCongr (YoungDiagram.card_ofPartition μ)) :
            ⨂[k]^(YoungDiagram.ofPartition μ).card (Fin n → k) →ₗ[k] ⨂[k]^d (Fin n → k)) =
      LinearMap.range ((permTensorAction k n d).asAlgebraHom (μ.youngSymmetrizer k)) := by
  rw [weylModuleOfShape_toSubmodule, permTensorActionAlgHom_def,
    map_reindex_range_permTensorAction_asAlgebraHom, Nat.Partition.youngSymmetrizer_def]

/-- **The Weyl module of the shape of `μ` as the image of `c_μ`**: relabeling the tensor factors
is an equivalence of representations of `GL n k` from `𝕊^μ(kⁿ)` onto `c_μ (kⁿ)^{⊗d}`. -/
noncomputable def weylRepOfShapeEquivRange (μ : d.Partition) :
    (weylRepOfShape k n (YoungDiagram.ofPartition μ)).Equiv
      ((tensorPowerRep k n d).subrepresentation
        (LinearMap.range ((permTensorAction k n d).asAlgebraHom (μ.youngSymmetrizer k)))
        (range_asAlgebraHom_permTensorAction_le_comap k n d _)) :=
  .mk (((PiTensorProduct.reindex k (fun _ => Fin n → k)
      (finCongr (YoungDiagram.card_ofPartition μ))).submoduleMap _).trans
      (LinearEquiv.ofEq _ _ (map_reindex_weylModuleOfShape k n d μ)))
    fun g => by
      ext x
      -- relabeling the tensor factors commutes with `g^{⊗d}`
      simpa using (PiTensorProduct.map_reindex (fun _ => (g : Matrix (Fin n) (Fin n) k).mulVecLin)
        (finCongr (YoungDiagram.card_ofPartition μ)) (x : ⨂[k]^_ (Fin n → k))).symm

/-- The equivalence `TauCeti.weylRepOfShapeEquivRange` relabels the tensor factors. -/
@[simp]
theorem coe_weylRepOfShapeEquivRange_apply (μ : d.Partition)
    (w : (weylModuleOfShape k n (YoungDiagram.ofPartition μ)).toSubmodule) :
    (weylRepOfShapeEquivRange k n d μ w : ⨂[k]^d (Fin n → k)) =
      PiTensorProduct.reindex k (fun _ => Fin n → k)
        (finCongr (YoungDiagram.card_ofPartition μ)) w :=
  (rfl)

end CommRing

variable [Field k] [CharZero k]

/-- **The Schur-Weyl decomposition of `(kⁿ)^{⊗d}`.** Over a field of characteristic zero,
`⨁_{μ ⊢ d} k[S_d] c_μ ⊗ 𝕊^μ(kⁿ) ≅ (kⁿ)^{⊗d}` as representations of `S_d × GL n k`, where
`k[S_d] c_μ` is the Specht module of `μ` in its ideal presentation, on which `S_d` acts by left
multiplication, and `𝕊^μ(kⁿ)` is the Weyl module of the shape of `μ`, on which `GL n k` acts. The
summand `a ⊗ w` of `μ` goes to `a · w`, with `w` read in `(kⁿ)^{⊗d}` by relabeling its tensor
factors (`TauCeti.schurWeylEquiv_lof_tmul`). -/
noncomputable def schurWeylEquiv :
    (Representation.directSum fun μ : d.Partition => Representation.tprod
      ((Representation.ofModule' (k := k) (G := Equiv.Perm (Fin d))
        (Ideal.span {μ.youngSymmetrizer k} : Ideal (MonoidAlgebra k (Equiv.Perm (Fin d))))).comp
          (MonoidHom.fst _ (GL (Fin n) k)))
      ((weylRepOfShape k n (YoungDiagram.ofPartition μ)).comp
          (MonoidHom.snd (Equiv.Perm (Fin d)) _))).Equiv
      (permTensorPowerRep k n d) :=
  .mk ((DirectSum.congrLinearEquiv fun μ => TensorProduct.congr (LinearEquiv.refl k _)
      (weylRepOfShapeEquivRange k n d μ).toLinearEquiv).trans
      (LinearEquiv.ofBijective _ (permTensorAction k n d).youngSymmetrizerEval_bijective))
    fun ⟨σ, g⟩ => by
      refine DirectSum.linearMap_ext k fun μ => TensorProduct.ext' fun a w => ?_
      have h := commute_permTensorActionAlgHom_tensorPowerRep k n d a g
      rw [permTensorActionAlgHom_def] at h
      simp only [LinearMap.coe_comp, Function.comp_apply, Representation.directSum_apply,
        DirectSum.lmap_lof, Representation.tprod_apply, TensorProduct.map_tmul,
        MonoidHom.coe_comp, MonoidHom.coe_fst, MonoidHom.coe_snd, LinearEquiv.coe_coe,
        LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply, DirectSum.coe_congrLinearEquiv,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply, Representation.Equiv.toLinearEquiv_apply,
        Representation.IntertwiningMap.isIntertwining, Representation.subrepresentation_apply,
        LinearMap.coe_restrict_apply,
        Representation.youngSymmetrizerEval_lof_tmul,
        permTensorPowerRep_apply, mul_apply_eq_comp,
        TauCeti.Representation.ofModule'_apply, Submodule.coe_smul, smul_eq_mul, map_mul,
        Representation.asAlgebraHom_single_one]
      rw [← mul_apply_eq_comp _ ((tensorPowerRep k n d) g), h.eq, mul_apply_eq_comp]

/-- The Schur-Weyl decomposition sends `a ⊗ w` in the summand of `μ` to `a · w`. -/
@[simp]
theorem schurWeylEquiv_lof_tmul (μ : d.Partition)
    (a : (Ideal.span {μ.youngSymmetrizer k} : Ideal (MonoidAlgebra k (Equiv.Perm (Fin d)))))
    (w : (weylModuleOfShape k n (YoungDiagram.ofPartition μ)).toSubmodule) :
    schurWeylEquiv k n d (DirectSum.lof k d.Partition _ μ (a ⊗ₜ w)) =
      (permTensorAction k n d).asAlgebraHom (a : MonoidAlgebra k (Equiv.Perm (Fin d)))
        (PiTensorProduct.reindex k (fun _ => Fin n → k)
          (finCongr (YoungDiagram.card_ofPartition μ)) w) := by
  simp [schurWeylEquiv, DirectSum.coe_congrLinearEquiv]

end TauCeti

namespace TauCeti

variable (n d : ℕ)

section Complex

/-- A summand of `TauCeti.schurWeylEquiv` whose shape has more than `n` rows is zero, since its
Weyl module is. -/
private theorem subsingleton_span_youngSymmetrizer_tensorProduct_weylModuleOfShape
    {μ : d.Partition} (hμ : n < μ.parts.card) :
    Subsingleton ((Ideal.span {μ.youngSymmetrizer ℂ} :
        Ideal (MonoidAlgebra ℂ (Equiv.Perm (Fin d)))) ⊗[ℂ]
      (weylModuleOfShape ℂ n (YoungDiagram.ofPartition μ)).toSubmodule) := by
  have : Subsingleton (weylModuleOfShape ℂ n (YoungDiagram.ofPartition μ)).toSubmodule := by
    rw [Submodule.subsingleton_iff_eq_bot, (weylModuleOfShape_eq_bot_iff ℂ n _).mpr
      (by rwa [YoungDiagram.colLen_zero_ofPartition]), Subrepresentation.toSubmodule_bot]
  infer_instance

/-- The summand `ℂ[S_d] c_μ ⊗ 𝕊^μ(ℂⁿ)` of `TauCeti.schurWeylEquiv` at `μ`. -/
private abbrev schurWeylSummand (μ : d.Partition) : Type :=
  (Ideal.span {μ.youngSymmetrizer ℂ} : Ideal (MonoidAlgebra ℂ (Equiv.Perm (Fin d)))) ⊗[ℂ]
    (weylModuleOfShape ℂ n (YoungDiagram.ofPartition μ)).toSubmodule

/-- The linear equivalence inverse to `TauCeti.schurWeylDecomposition`: replace each complex
Specht module by the ideal `ℂ[S_d] c_μ`, add the zero summands of the shapes with more than `n`
rows, and apply `TauCeti.schurWeylEquiv`. -/
private noncomputable def schurWeylDecompositionLinearEquiv :
    (⨁ μ : {μ : d.Partition // μ.parts.card ≤ n},
      (spechtModuleℂ μ.1).V ⊗[ℂ] (schurFunctor n (YoungDiagram.ofPartition μ.1)).V) ≃ₗ[ℂ]
      ⨂[ℂ]^d (Fin n → ℂ) :=
  ((DirectSum.congrLinearEquiv fun μ => TensorProduct.congr
      μ.1.spanYoungSymmetrizerEquivSpechtModuleℂ.symm.toLinearEquiv (LinearEquiv.refl ℂ _)).trans
    (DirectSum.restrictSubtypeLinearEquiv (schurWeylSummand n d) (fun μ => μ.parts.card ≤ n)
      fun _ hμ =>
      subsingleton_span_youngSymmetrizer_tensorProduct_weylModuleOfShape n d
        (lt_of_not_ge hμ)).symm).trans
    (schurWeylEquiv ℂ n d).toLinearEquiv

/-- The linear equivalence `schurWeylDecompositionLinearEquiv` on a pure tensor of a summand. -/
private theorem schurWeylDecompositionLinearEquiv_lof_tmul
    (μ : {μ : d.Partition // μ.parts.card ≤ n})
    (s : spechtModuleℂ μ.1) (w : schurFunctor n (YoungDiagram.ofPartition μ.1)) :
    schurWeylDecompositionLinearEquiv n d (DirectSum.lof ℂ _ _ μ (s ⊗ₜ w)) =
      schurWeylEquiv ℂ n d (DirectSum.lof ℂ d.Partition _ μ.1
        (μ.1.spanYoungSymmetrizerEquivSpechtModuleℂ.symm s ⊗ₜ w)) := by
  simp [schurWeylDecompositionLinearEquiv, DirectSum.coe_congrLinearEquiv]

/-- The linear equivalence `schurWeylDecompositionLinearEquiv` intertwines the actions of
`S_d × GL n ℂ`. -/
private theorem schurWeylDecompositionLinearEquiv_comp (σg : Equiv.Perm (Fin d) × GL (Fin n) ℂ) :
    (schurWeylDecompositionLinearEquiv n d).toLinearMap ∘ₗ
        Representation.directSum (fun μ : {μ : d.Partition // μ.parts.card ≤ n} =>
          Representation.tprod ((spechtModuleℂ μ.1).ρ.comp (MonoidHom.fst _ (GL (Fin n) ℂ)))
            ((schurFunctor n (YoungDiagram.ofPartition μ.1)).ρ.comp
              (MonoidHom.snd (Equiv.Perm (Fin d)) _))) σg =
      permTensorPowerRep ℂ n d σg ∘ₗ (schurWeylDecompositionLinearEquiv n d).toLinearMap := by
  obtain ⟨σ, g⟩ := σg
  refine DirectSum.linearMap_ext ℂ fun μ => TensorProduct.ext' fun s w => ?_
  -- move the action of `σ` from the complex Specht module to the ideal `ℂ[S_d] c_μ`
  have he := Representation.IntertwiningMap.isIntertwining _ _
    μ.1.spanYoungSymmetrizerEquivSpechtModuleℂ.symm.toIntertwiningMap σ s
  have hsw := Representation.IntertwiningMap.isIntertwining _ _
    (schurWeylEquiv ℂ n d).toIntertwiningMap (σ, g)
    (DirectSum.lof ℂ d.Partition _ μ.1 (μ.1.spanYoungSymmetrizerEquivSpechtModuleℂ.symm s ⊗ₜ w))
  simp only [Representation.Equiv.coe_toIntertwiningMap] at he hsw
  simp only [Representation.directSum_apply, DirectSum.lmap_lof, Representation.tprod_apply,
    TensorProduct.map_tmul, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd] at hsw
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Representation.directSum_apply,
    DirectSum.lmap_lof, Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.comp_apply,
    MonoidHom.coe_fst, MonoidHom.coe_snd]
  rw [schurWeylDecompositionLinearEquiv_lof_tmul, schurWeylDecompositionLinearEquiv_lof_tmul, he,
    FDRep.of_ρ']
  exact hsw

/-- **The Schur-Weyl decomposition of `(ℂⁿ)^{⊗d}` into complex Specht modules and Schur
functors.** As representations of `S_d × GL n ℂ`,

`(ℂⁿ)^{⊗d} ≅ ⨁_{μ ⊢ d, ℓ(μ) ≤ n} S^μ_ℂ ⊗ 𝕊^μ(ℂⁿ)`,

where `S^μ_ℂ` is the complex Specht module (`TauCeti.spechtModuleℂ`), on which `S_d` acts, and
`𝕊^μ(ℂⁿ)` is the Schur functor (`TauCeti.schurFunctor`), on which `GL n ℂ` acts. The sum runs over
the partitions with at most `n` parts: the Schur functors of the other shapes vanish. The inverse
sends the summand `s ⊗ w` of `μ` to `a · w`, where `a ∈ ℂ[S_d] c_μ` corresponds to `s` under
`Nat.Partition.spanYoungSymmetrizerEquivSpechtModuleℂ` and `w` is read in `(ℂⁿ)^{⊗d}` by
relabeling its tensor factors (`TauCeti.schurWeylDecomposition_symm_lof_tmul`). Restricting to the
two factors of `S_d × GL n ℂ` gives the two equivariances separately. -/
noncomputable def schurWeylDecomposition :
    (permTensorPowerRep ℂ n d).Equiv
      (Representation.directSum fun μ : {μ : d.Partition // μ.parts.card ≤ n} =>
        Representation.tprod ((spechtModuleℂ μ.1).ρ.comp (MonoidHom.fst _ (GL (Fin n) ℂ)))
          ((schurFunctor n (YoungDiagram.ofPartition μ.1)).ρ.comp
            (MonoidHom.snd (Equiv.Perm (Fin d)) _))) :=
  .mk (schurWeylDecompositionLinearEquiv n d).symm
    (LinearEquiv.isIntertwining_symm_isIntertwining (schurWeylDecompositionLinearEquiv_comp n d))

/-- The inverse of the decomposition sends `s ⊗ w` in the summand of `μ` to `a · w`, where
`a ∈ ℂ[S_d] c_μ` corresponds to `s` and `w` is read in `(ℂⁿ)^{⊗d}` by relabeling its tensor
factors. -/
@[simp]
theorem schurWeylDecomposition_symm_lof_tmul (μ : {μ : d.Partition // μ.parts.card ≤ n})
    (s : spechtModuleℂ μ.1) (w : schurFunctor n (YoungDiagram.ofPartition μ.1)) :
    (schurWeylDecomposition n d).symm (DirectSum.lof ℂ _ _ μ (s ⊗ₜ w)) =
      (permTensorAction ℂ n d).asAlgebraHom
        (μ.1.spanYoungSymmetrizerEquivSpechtModuleℂ.symm s : MonoidAlgebra ℂ (Equiv.Perm (Fin d)))
        (PiTensorProduct.reindex ℂ (fun _ => Fin n → ℂ)
          (finCongr (YoungDiagram.card_ofPartition μ.1)) w) := by
  rw [schurWeylDecomposition, Representation.Equiv.mk_symm, Representation.Equiv.mk_apply,
    LinearEquiv.symm_symm, schurWeylDecompositionLinearEquiv_lof_tmul, schurWeylEquiv_lof_tmul]

/-- **The decomposition intertwines the symmetric groups**: the permutation of the tensor factors
of `(ℂⁿ)^{⊗d}` corresponds to the summand-wise action of `S_d` on the complex Specht modules. -/
theorem schurWeylDecomposition_comp_permTensorAction (σ : Equiv.Perm (Fin d)) :
    (schurWeylDecomposition n d).toLinearMap ∘ₗ permTensorAction ℂ n d σ =
      DirectSum.lmap (fun μ : {μ : d.Partition // μ.parts.card ≤ n} =>
          ((spechtModuleℂ μ.1).ρ σ).rTensor (schurFunctor n (YoungDiagram.ofPartition μ.1)).V) ∘ₗ
        (schurWeylDecomposition n d).toLinearMap := by
  have h := (schurWeylDecomposition n d).toIntertwiningMap.isIntertwining' (σ, 1)
  rw [permTensorPowerRep_apply, map_one (tensorPowerRep ℂ n d), mul_one] at h
  refine h.trans ?_
  congr 1
  refine DirectSum.linearMap_ext ℂ fun μ => TensorProduct.ext' fun s w => ?_
  simp

/-- **The decomposition intertwines the general linear groups**: the diagonal action of `GL n ℂ` on
`(ℂⁿ)^{⊗d}` corresponds to the summand-wise action on the Schur functors. -/
theorem schurWeylDecomposition_comp_tensorPowerRep (g : GL (Fin n) ℂ) :
    (schurWeylDecomposition n d).toLinearMap ∘ₗ tensorPowerRep ℂ n d g =
      DirectSum.lmap (fun μ : {μ : d.Partition // μ.parts.card ≤ n} =>
          ((schurFunctor n (YoungDiagram.ofPartition μ.1)).ρ g).lTensor (spechtModuleℂ μ.1).V) ∘ₗ
        (schurWeylDecomposition n d).toLinearMap := by
  have h := (schurWeylDecomposition n d).toIntertwiningMap.isIntertwining' (1, g)
  rw [permTensorPowerRep_apply, map_one (permTensorAction ℂ n d), one_mul] at h
  refine h.trans ?_
  congr 1
  refine DirectSum.linearMap_ext ℂ fun μ => TensorProduct.ext' fun s w => ?_
  simp

end Complex

end TauCeti

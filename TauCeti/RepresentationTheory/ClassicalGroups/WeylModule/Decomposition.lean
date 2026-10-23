/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Basic
public import TauCeti.RepresentationTheory.Symmetric.Specht.Decomposition

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

## Main definitions

* `TauCeti.weylRepOfShapeEquivRange`: the Weyl module of the shape of `μ` is the image of the Young
  symmetrizer `c_μ` in `(kⁿ)^{⊗d}`, as representations of `GL n k`.
* `TauCeti.schurWeylEquiv`: **the Schur-Weyl decomposition**
  `⨁_μ k[S_d] c_μ ⊗ 𝕊^μ(kⁿ) ≅ (kⁿ)^{⊗d}` of representations of `S_d × GL n k`.

## Main results

* `TauCeti.map_reindex_weylModuleOfShape`: relabeling the tensor factors carries the Weyl module of
  the shape of `μ` onto `c_μ (kⁿ)^{⊗d}`.

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
    map_reindex_range_asAlgebraHom, Nat.Partition.youngSymmetrizer_def]

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
        permTensorPowerRep_apply, Module.End.mul_apply,
        TauCeti.Representation.ofModule'_apply, Submodule.coe_smul, smul_eq_mul, map_mul,
        Representation.asAlgebraHom_single_one]
      rw [← Module.End.mul_apply _ ((tensorPowerRep k n d) g), h.eq, Module.End.mul_apply]

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

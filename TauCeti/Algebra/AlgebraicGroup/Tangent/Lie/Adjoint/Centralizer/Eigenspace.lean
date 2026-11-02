/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Differential
public import TauCeti.Algebra.Coalgebra.Subcomodule.Comap
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
public import TauCeti.Algebra.Lie.Sl2.EigenspaceMap

/-!
# Eigenspaces of `ad x` as representations of the centralizer of `x`

Let `G = Spec H` be an affine group over a field `k` with Lie algebra `𝔤`, let `x ∈ 𝔤`, and let
`K ⊆ C_G(x)` be a closed subgroup of the centralizer of `x`, cut out by a Hopf ideal `J`
containing the centralizer ideal `TauCeti.centralizerHopfIdeal H x`. Restrict the adjoint
representation of `G` to `K`, that is, corestrict the adjoint coaction along `H → H ⧸ J`. Every
point of `K` acts on `𝔤` by a Lie algebra automorphism fixing `x`, so it commutes with `ad x`.
Hence `ad x` is an endomorphism of this representation of `K` (`TauCeti.centralizerAdHom`), and
each eigenspace `𝔤(μ) = ker (ad x - μ)` is a subrepresentation of `K`, with the
scheme-theoretic restricted coaction (`Comodule.Hom.eigenspace`). The equivariance holds over
every commutative value algebra, including nonreduced ones.

The differentiated action of the Lie algebra of `K` on `𝔤` is the bracket: a tangent vector `d`
of `K` acts by `⁅d, -⁆`, where `d` is viewed in `𝔤` through the differential of the inclusion
`K ↪ G` (`TauCeti.differential_corestrict_adjointComodule`).

For an `sl₂` triple `(h, e, f)` in `𝔤` over a field of characteristic zero take `K = C_G(h)`.
Its Lie algebra is `𝔤(0) = ker (ad h)`, it acts on the grade-two space `𝔤(2)`, and the
differential at `e` of the orbit map of this action is `y ↦ ⁅y, e⁆`. The identity
`⁅𝔤(0), e⁆ = 𝔤(2)` (`IsSl2Triple.map_ad_e_eigenspace_zero`) says that this differential is onto
(`IsSl2Triple.range_differential_flip_eigenspace_two_eq_top`). Over an algebraically closed field
of characteristic zero, a vector at which the orbit differential is onto has an open orbit, so this
is the hypothesis that makes `C_G(h) • e` open in `𝔤(2)`; the openness itself is not proved here.
That open orbit is how one shows that two nilpotent elements with the same weighted Dynkin diagram
are conjugate.

## Main declarations

* `TauCeti.centralizerAdHom`: `ad x` as an endomorphism of the adjoint representation restricted
  to a closed subgroup of `C_G(x)`.
* `TauCeti.differential_centralizerAdHom_eigenspace`: the same on an eigenspace of `ad x`.
* `IsSl2Triple.range_differential_flip_eigenspace_two_eq_top`: the orbit differential of `e` for
  the action of `C_G(h)` on `𝔤(2)` is onto.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §3.4 and §3.5: the action of the centralizer of `h` on `𝔤(2)`.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

attribute [local instance] Derivation.adjointComodule

section Corestrict

variable (J : HopfIdeal k H)

/-- The adjoint coaction corestricted to the closed subgroup cut out by `J` is the flipped point
action of the quotient map `H → H ⧸ J`. -/
private theorem corestrictCoact_adjointComodule_eq
    (y : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    Comodule.corestrictCoact (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom y =
      TensorProduct.comm k (H ⧸ J.toIdeal) _
        (Comodule.endOfPoint (Module.Dual k (Bialgebra.CotangentSpace k H))
          (Ideal.Quotient.mkₐ k J.toIdeal) (1 ⊗ₜ[k] y)) := by
  rw [Comodule.endOfPoint_tmul, one_smul, TensorProduct.comm_comm, Comodule.corestrictCoact_apply,
    LinearMap.lTensor_def]
  -- The quotient bialgebra map is `Ideal.Quotient.mkₐ` with its coalgebra structure recorded.
  congr 2

variable {J} (x : Module.Dual k (Bialgebra.CotangentSpace k H))

/-- **`ad x` is equivariant for the centralizer of `x`.** On the adjoint representation restricted
to a closed subgroup of the centralizer `C_G(x)`, cut out by a Hopf ideal `J` containing the
centralizer ideal, the endomorphism `ad x` is a morphism of representations. -/
noncomputable def centralizerAdHom (hJ : centralizerHopfIdeal H x ≤ J) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
    Comodule.Hom k (H ⧸ J.toIdeal) (Module.Dual k (Bialgebra.CotangentSpace k H))
      (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
  letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
    (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
  { toLinearMap := LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x
    map_coact := by
      -- The quotient point lies in `C_G(x)`, so its adjoint action fixes `1 ⊗ x` and hence
      -- commutes with `ad x`.
      let g : HopfAlgebra.points (H := H) (CommAlgCat.of k (H ⧸ J.toIdeal)) :=
        toConv (Ideal.Quotient.mkₐ k J.toIdeal)
      have hfix : Comodule.endOfPoint (Module.Dual k (Bialgebra.CotangentSpace k H)) g.ofConv
          (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] x := by
        rw [← Comodule.stabilizerHopfIdeal_le_ker_iff, ← centralizerHopfIdeal_def]
        intro a ha
        rw [RingHom.mem_ker]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJ ha)
      refine LinearMap.ext fun y ↦ ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Comodule.corestrict_coact,
        corestrictCoact_adjointComodule_eq, corestrictCoact_adjointComodule_eq,
        ← LinearMap.rTensor_def, LinearMap.rTensor_comm]
      congr 1
      rw [← LinearMap.baseChange_eq_lTensor, ← LinearMap.baseChange_tmul]
      exact (LinearMap.congr_fun
        (Derivation.endOfPoint_adjointComodule_comp_baseChange_ad _ g x hfix) _).symm }

/-- `TauCeti.centralizerAdHom` acts by the bracket with `x`. -/
@[simp]
theorem centralizerAdHom_apply (hJ : centralizerHopfIdeal H x ≤ J)
    (y : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
    centralizerAdHom x hJ y = ⁅x, y⁆ :=
  (rfl)

/-- The underlying linear map of `TauCeti.centralizerAdHom` is `ad x`. -/
@[simp]
theorem centralizerAdHom_toLinearMap (hJ : centralizerHopfIdeal H x ≤ J) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
    (centralizerAdHom x hJ).toLinearMap =
      LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x :=
  (rfl)

/-- A tangent vector `d` of a closed subgroup of `C_G(x)` acts on an eigenspace of `ad x` by the
bracket with its image in `𝔤`. -/
theorem differential_centralizerAdHom_eigenspace (hJ : centralizerHopfIdeal H x ≤ J) (μ : k)
    (d : Derivation k (H ⧸ J.toIdeal) (Bialgebra.CounitAlgebra k (H ⧸ J.toIdeal) k))
    (y : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
    ∀ hy : y ∈ (centralizerAdHom x hJ).eigenspace μ,
      (Comodule.differential (R := k) (H := H ⧸ J.toIdeal)
          (M := (centralizerAdHom x hJ).eigenspace μ) d ⟨y, hy⟩ :
          Module.Dual k (Bialgebra.CotangentSpace k H)) =
        ⁅(Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm (J.quotientLieHom d), y⁆ := by
  let := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
    (Bialgebra.Quotient.mkBialgHom (R := k) J.toIdeal).toCoalgHom
  intro hy
  rw [← differential_corestrict_adjointComodule, ← Subcomodule.subtype_apply,
    Comodule.Hom.map_differential, Subcomodule.subtype_apply]

end Corestrict

end TauCeti

namespace IsSl2Triple

open TauCeti

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

attribute [local instance] Derivation.adjointComodule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {h e f : Module.Dual k (Bialgebra.CotangentSpace k H)}

/-- The nilpositive element `e` of an `sl₂` triple lies in the grade-two eigenspace of `ad h`,
regarded as a representation of `C_G(h)`. -/
theorem e_mem_eigenspace_two (t : IsSl2Triple h e f) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) (centralizerHopfIdeal H h).toIdeal).toCoalgHom
    e ∈ (centralizerAdHom h le_rfl).eigenspace 2 := by
  let := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
    (Bialgebra.Quotient.mkBialgHom (R := k) (centralizerHopfIdeal H h).toIdeal).toCoalgHom
  rw [Comodule.Hom.mem_eigenspace_iff, centralizerAdHom_apply]
  exact t.lie_h_e_smul k

/-- **The orbit differential on the grade-two space is onto.** For an `sl₂` triple `(h, e, f)` in
the Lie algebra `𝔤` of an affine group `G` over a field of characteristic zero, consider the
centralizer `C_G(h)` acting on the eigenspace `𝔤(2)` of `ad h`. The differential at `e` of its
orbit map, `d ↦ d • e`, is onto `𝔤(2)`, because `⁅𝔤(0), e⁆ = 𝔤(2)` and the Lie algebra of
`C_G(h)` is `𝔤(0) = ker (ad h)`. -/
theorem range_differential_flip_eigenspace_two_eq_top [CharZero k] (t : IsSl2Triple h e f) :
    letI := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
      (Bialgebra.Quotient.mkBialgHom (R := k) (centralizerHopfIdeal H h).toIdeal).toCoalgHom
    LinearMap.range ((Comodule.differential (R := k) (H := H ⧸ (centralizerHopfIdeal H h).toIdeal)
        (M := (centralizerAdHom h le_rfl).eigenspace 2)).toLinearMap.flip
        ⟨e, t.e_mem_eigenspace_two⟩) = ⊤ := by
  let := Comodule.Corestrict (M := Module.Dual k (Bialgebra.CotangentSpace k H))
    (Bialgebra.Quotient.mkBialgHom (R := k) (centralizerHopfIdeal H h).toIdeal).toCoalgHom
  rw [eq_top_iff]
  rintro ⟨z, hz⟩ -
  -- Write `z = ⁅e, y⁆` with `y ∈ 𝔤(0)`, and realize `-y` as a tangent vector of `C_G(h)`.
  rw [Comodule.Hom.mem_eigenspace_iff, centralizerAdHom_apply] at hz
  have hz' : z ∈ (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) h).eigenspace 2 :=
    Module.End.mem_eigenspace_iff.mpr hz
  rw [← t.map_ad_e_eigenspace_zero] at hz'
  obtain ⟨y, hy, rfl⟩ := hz'
  have hy' : ⁅h, -y⁆ = 0 := by
    have hy0 := Module.End.mem_eigenspace_iff.mp hy
    rw [LieAlgebra.ad_apply, zero_smul] at hy0
    rw [lie_neg, hy0, neg_zero]
  have hmem : Derivation.cotangentDualLieEquiv (R := k) (H := H) (-y) ∈
      (centralizerHopfIdeal H h).lieSubalgebra (B := k) := by
    rw [mem_lieSubalgebra_centralizerHopfIdeal_iff,
      ← (Derivation.cotangentDualLieEquiv (R := k) (H := H)).map_lie, hy', map_zero]
  let d := (HopfIdeal.quotientLieEquiv (B := k) (centralizerHopfIdeal H h)).symm ⟨_, hmem⟩
  have hd : (centralizerHopfIdeal H h).quotientLieHom d =
      Derivation.cotangentDualLieEquiv (R := k) (H := H) (-y) := by
    rw [← HopfIdeal.quotientLieEquiv_apply_coe, LieEquiv.apply_symm_apply]
  refine ⟨d, Subtype.ext ?_⟩
  rw [LinearMap.flip_apply, LieHom.coe_toLinearMap, differential_centralizerAdHom_eigenspace,
    hd, LieEquiv.symm_apply_apply, neg_lie, ← lie_skew, neg_neg]
  exact (LieAlgebra.ad_apply (R := k) (L := Module.Dual k (Bialgebra.CotangentSpace k H)) e y).symm

end IsSl2Triple

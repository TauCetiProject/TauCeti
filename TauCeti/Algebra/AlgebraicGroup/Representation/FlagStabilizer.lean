/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Basis.Flag
public import TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
public import TauCeti.Algebra.AlgebraicGroup.Representation.TensorProduct
public import TauCeti.Algebra.Coalgebra.Comodule.Transport
public import TauCeti.LinearAlgebra.ExteriorPower.FlagCone
import Mathlib.RingTheory.HopfAlgebra.Quotient
import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra.Corestrict
import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Corestrict
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Solvable
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Flag comodules and scheme-theoretic stabilizers of exterior flag lines

For a comodule `M` over a commutative bialgebra `H`, each exterior power `⋀ᵈ M` is an `H`-comodule
(`TauCeti.Comodule.exteriorPower`), and transporting tensor products along `flagSpaceZeroEquiv` and
`flagSpaceSuccEquiv` equips `exteriorPower.FlagSpace R M d` with an `H`-comodule structure
(`TauCeti.Comodule.exteriorFlag`) whose rational point action is `exteriorFlagMap d`.

Over a field `k` and a commutative Hopf algebra `H`:
* the line stabilizer of a nonzero pure tensor `m ⊗ₜ n` is the supremum of the line stabilizers of
  `m` and `n` (`Submodule.stabilizerHopfIdeal_span_singleton_tmul`), cutting out the intersection of
  their closed stabilizer subgroup schemes even when `H` or the stabilizers are nonreduced;
* the line stabilizer of `exteriorFlagVector k d b` for a basis `b : Module.Basis (Fin d) k M` is
  `Finset.univ.sup fun r ↦ (b.flag r).stabilizerHopfIdeal H`, and lies below `J : HopfIdeal k H`
  precisely when the corestricted coefficient matrix of `b` over `H ⧸ J` is upper triangular;
* if `M` contains any subspace `W₀` whose stabilizer `J` has solvable `k`-points, then for *every*
  basis `b` of `M`, the `k`-points of the quotient by
  `(k ∙ exteriorFlagVector k d b).stabilizerHopfIdeal H` form a solvable group
  (`isSolvable_points_quotient_stabilizerHopfIdeal_exteriorFlagVector`), since acting on `M` maps
  it into `upperTriangularGroup (Fin d) k` with kernel fixing `W₀`.

## Main definitions

* `TauCeti.Comodule.exteriorFlag`: the `H`-comodule structure on `exteriorPower.FlagSpace R M d`.

## Main results

* `TauCeti.Comodule.basePointsRepresentation_exteriorFlag`: base-valued points act on `FlagSpace`
  by `exteriorPower.exteriorFlagMap`.
* `Submodule.stabilizerHopfIdeal_eq_of_forall_mem_quotientPointsSubgroup_iff`: point-functor
  characterization of `W.stabilizerHopfIdeal H = I`.
* `Submodule.stabilizerHopfIdeal_span_singleton_tmul`: the line stabilizer of `m ⊗ₜ n` (`m, n ≠ 0`)
  is `(k ∙ m).stabilizerHopfIdeal H ⊔ (k ∙ n).stabilizerHopfIdeal H`.
* `TauCeti.Comodule.stabilizerHopfIdeal_span_exteriorFlagVector`: the line stabilizer of
  `exteriorFlagVector k d b` is `Finset.univ.sup fun r ↦ (b.flag r).stabilizerHopfIdeal H`.
* `TauCeti.Comodule.stabilizerHopfIdeal_le_iff_exists_subcomodule_corestrict`:
  `W.stabilizerHopfIdeal H ≤ J` iff `W` arises from a subcomodule over `H ⧸ J.toIdeal`.
* `TauCeti.Comodule.stabilizerHopfIdeal_span_exteriorFlagVector_le_iff`: the line stabilizer lies
  below `J` iff `coefficientMatrix (C := H ⧸ J.toIdeal) b` is upper triangular.
* `TauCeti.Comodule.stabilizerHopfIdeal_span_exteriorFlagVector_eq`: when `b` is upper triangular
  over `H ⧸ J.toIdeal` and `(k ∙ b 0).stabilizerHopfIdeal H = J`, the flag line stabilizer equals
  `J`.
* `TauCeti.Comodule.isSolvable_points_quotient_stabilizerHopfIdeal_exteriorFlagVector`: solvability
  of `k`-points for the stabilizer of any basis flag vector in `M`.

## References

* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), Theorem 17.9(a), p. 354.
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, Springer (1975), §21.3.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.Comodule

section Bialgebra

variable (R H M : Type*) [CommRing R] [CommSemiring H] [Bialgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M]

/-- The right `H`-comodule structure on `exteriorPower.FlagSpace R M d`, built recursively from
`Comodule.exteriorPower` and `Comodule.tensor` via `Comodule.Transport`. Select it explicitly as a
local instance. -/
@[implicit_reducible]
noncomputable def exteriorFlag : (d : ℕ) → Comodule R H (exteriorPower.FlagSpace R M d)
  | 0 =>
      let _ : Comodule R H (⋀[R]^0 M) := exteriorPower R H M 0
      Transport (exteriorPower.flagSpaceZeroEquiv R M).symm
  | r + 1 =>
      let _ : Comodule R H (exteriorPower.FlagSpace R M r) := exteriorFlag r
      let _ : Comodule R H (⋀[R]^(r + 1) M) := exteriorPower R H M (r + 1)
      let _ : Comodule R H (exteriorPower.FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M) :=
        tensor R H (exteriorPower.FlagSpace R M r) (⋀[R]^(r + 1) M)
      Transport (exteriorPower.flagSpaceSuccEquiv R M r).symm

end Bialgebra

section Points

variable {R H M N : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M]
  [AddCommGroup N] [Module R N]

/-- Transporting a comodule along a linear equivalence conjugates its base-point representation. -/
theorem basePointsRepresentation_transport (e : M ≃ₗ[R] N) (g : WithConv (H →ₐ[R] R)) :
    (letI : Comodule R H N := Transport (R := R) (C := H) e
     basePointsRepresentation (R := R) (H := H) N g) =
      e.toLinearMap ∘ₗ basePointsRepresentation (R := R) (H := H) M g ∘ₗ e.symm.toLinearMap := by
  let _ : Comodule R H N := Transport (R := R) (C := H) e
  ext n
  have h := LinearMap.congr_fun
    (baseChange_comp_endOfPoint (transportToHom (R := R) (C := H) e) g.ofConv) (1 ⊗ₜ[R] e.symm n)
  simp only [LinearMap.comp_apply, transportToHom_toLinearMap, LinearMap.baseChange_tmul,
    endOfPoint_tmul, one_smul, endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation] at h
  simpa using congrArg (TensorProduct.lid R N) h.symm

/-- Base-valued points act on the `n`th exterior power by `exteriorPower.map n`. -/
theorem basePointsRepresentation_exteriorPower (n : ℕ) (g : WithConv (H →ₐ[R] R)) :
    (letI : Comodule R H (⋀[R]^n M) := exteriorPower R H M n
     basePointsRepresentation (R := R) (H := H) (⋀[R]^n M) g) =
      _root_.exteriorPower.map n (basePointsRepresentation (R := R) (H := H) M g) := by
  let _ : Comodule R H (⋀[R]^n M) := exteriorPower R H M n
  refine _root_.exteriorPower.linearMap_ext (R := R) (M := M) (n := n) ?_
  ext v
  simp only [LinearMap.compAlternatingMap_apply, _root_.exteriorPower.map_apply_ιMulti]
  have h := congrArg (Algebra.TensorProduct.lid R (ExteriorAlgebra R M))
    (baseChange_subtype_endOfPoint_ιMulti (R := R) (H := H) (M := M) n g.ofConv (1 : R) v)
  simp only [endOfPoint_tmul, one_smul, endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation,
    LinearMap.baseChange_tmul, map_list_prod, List.map_ofFn, Function.comp_def,
    Algebra.TensorProduct.lid_tmul, Submodule.subtype_apply] at h
  simpa only [_root_.exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    Function.comp_def] using h

/-- Base-valued points act on `exteriorPower.FlagSpace R M d` by
`exteriorPower.exteriorFlagMap d`. -/
theorem basePointsRepresentation_exteriorFlag (d : ℕ) (g : WithConv (H →ₐ[R] R)) :
    (letI : Comodule R H (exteriorPower.FlagSpace R M d) := exteriorFlag R H M d
     basePointsRepresentation (R := R) (H := H) (exteriorPower.FlagSpace R M d) g) =
      exteriorPower.exteriorFlagMap d (basePointsRepresentation (R := R) (H := H) M g) := by
  induction d with
  | zero =>
    let _ : Comodule R H (⋀[R]^0 M) := exteriorPower R H M 0
    change (letI : Comodule R H (exteriorPower.FlagSpace R M 0) :=
        Transport (exteriorPower.flagSpaceZeroEquiv R M).symm
      basePointsRepresentation (exteriorPower.FlagSpace R M 0) g) = _
    rw [basePointsRepresentation_transport, basePointsRepresentation_exteriorPower,
      exteriorPower.exteriorFlagMap_zero]
    rfl
  | succ r ih =>
    let _ : Comodule R H (exteriorPower.FlagSpace R M r) := exteriorFlag R H M r
    let _ : Comodule R H (⋀[R]^(r + 1) M) := exteriorPower R H M (r + 1)
    let _ : Comodule R H (exteriorPower.FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M) :=
      tensor R H (exteriorPower.FlagSpace R M r) (⋀[R]^(r + 1) M)
    change (letI : Comodule R H (exteriorPower.FlagSpace R M (r + 1)) :=
        Transport (exteriorPower.flagSpaceSuccEquiv R M r).symm
      basePointsRepresentation (exteriorPower.FlagSpace R M (r + 1)) g) = _
    rw [basePointsRepresentation_transport, exteriorPower.exteriorFlagMap_succ]
    congr 1
    congr 1
    apply TensorProduct.ext'
    intro x y
    rw [basePointsRepresentation_tensor_tmul, ih, basePointsRepresentation_exteriorPower,
      TensorProduct.map_tmul]

end Points

end TauCeti.Comodule

section StabilizerLemmas

open TauCeti

universe u v w₁ w₂

section PureTensorSpan

variable {A U V : Type*} [CommRing A] [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]

/-- Over a commutative ring, if `u₀` and `v₀` are unimodular, a pure tensor `u ⊗ₜ v` spans the same
line as `u₀ ⊗ₜ v₀` precisely when `u` spans `A ∙ u₀` and `v` spans `A ∙ v₀`. -/
private theorem span_singleton_tmul_eq_iff_of_isUnimodular {u u₀ : U} {v v₀ : V}
    (hu₀ : Module.IsUnimodular A u₀) (hv₀ : Module.IsUnimodular A v₀) :
    A ∙ (u ⊗ₜ[A] v) = A ∙ (u₀ ⊗ₜ[A] v₀) ↔ A ∙ u = A ∙ u₀ ∧ A ∙ v = A ∙ v₀ := by
  obtain ⟨φ₀, hφ₀⟩ := Module.isUnimodular_iff.mp hu₀
  obtain ⟨ψ₀, hψ₀⟩ := Module.isUnimodular_iff.mp hv₀
  simp only [le_antisymm_iff, Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have ha_v : a • v₀ = φ₀ u • v := by
      simpa [hφ₀] using congrArg ((TensorProduct.lid A V).toLinearMap ∘ₗ LinearMap.rTensor V φ₀) ha
    have hb_v : (b * φ₀ u) • v = v₀ := by
      simpa [hφ₀, mul_smul] using
        congrArg ((TensorProduct.lid A V).toLinearMap ∘ₗ LinearMap.rTensor V φ₀) hb
    have ha_u : a • u₀ = ψ₀ v • u := by
      simpa [hψ₀] using congrArg ((TensorProduct.rid A U).toLinearMap ∘ₗ LinearMap.lTensor U ψ₀) ha
    have hb_u : (b * ψ₀ v) • u = u₀ := by
      simpa [hψ₀, mul_smul] using
        congrArg ((TensorProduct.rid A U).toLinearMap ∘ₗ LinearMap.lTensor U ψ₀) hb
    have hprod : b * (φ₀ u * ψ₀ v) = 1 := by
      simpa [hψ₀, smul_eq_mul, mul_assoc] using congrArg ψ₀ hb_v
    refine ⟨⟨⟨b * φ₀ u * a, ?_⟩, ⟨b * ψ₀ v, hb_u⟩⟩, ⟨⟨b * ψ₀ v * a, ?_⟩, ⟨b * φ₀ u, hb_v⟩⟩⟩
    · rw [mul_smul, ha_u, ← mul_smul, mul_assoc, hprod, one_smul]
    · rw [mul_smul, ha_v, ← mul_smul, mul_right_comm b (ψ₀ v) (φ₀ u), mul_assoc, hprod, one_smul]
  · rintro ⟨⟨⟨r₁, rfl⟩, ⟨s₁, hs₁⟩⟩, ⟨⟨r₂, rfl⟩, ⟨s₂, hs₂⟩⟩⟩
    refine ⟨⟨r₁ * r₂, (TensorProduct.smul_tmul_smul r₁ r₂ u₀ v₀).symm⟩, ⟨s₁ * s₂, ?_⟩⟩
    rw [← TensorProduct.smul_tmul_smul s₁ s₂ (r₁ • u₀) (r₂ • v₀), hs₁, hs₂]

end PureTensorSpan

namespace Submodule

variable {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]

private theorem hopfIdeal_eq_of_forall_quotient_le_ker
    {I₁ I₂ : HopfIdeal k H}
    (h : ∀ (A : Type v) [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)),
      I₁.toIdeal ≤ RingHom.ker g.ofConv ↔ I₂.toIdeal ≤ RingHom.ker g.ofConv) :
    I₁ = I₂ := by
  ext x
  change x ∈ I₁.toIdeal ↔ x ∈ I₂.toIdeal
  have hle (J₁ J₂ : HopfIdeal k H)
      (hJ : ∀ (A : Type v) [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)),
        J₁.toIdeal ≤ RingHom.ker g.ofConv → J₂.toIdeal ≤ RingHom.ker g.ofConv) :
      J₂.toIdeal ≤ J₁.toIdeal := by
    have hker : RingHom.ker (Ideal.Quotient.mkₐ k J₁.toIdeal) = J₁.toIdeal := by
      rw [← RingHom.ker_coe_toRingHom]
      exact Ideal.Quotient.mkₐ_ker k J₁.toIdeal
    simpa [hker] using hJ (H ⧸ J₁.toIdeal) (toConv (Ideal.Quotient.mkₐ k J₁.toIdeal))
      (by simp [hker])
  exact SetLike.ext_iff.mp (le_antisymm
    (hle I₂ I₁ fun A _ _ g hg ↦ (h A g).mpr hg)
    (hle I₁ I₂ fun A _ _ g hg ↦ (h A g).mp hg)) x

/-- A subspace `W` of a comodule has stabilizer Hopf ideal `I` when every `H`-point in the universe
of `H` lies in the `I`-quotient points subgroup if and only if it stabilizes `W`. -/
theorem stabilizerHopfIdeal_eq_of_forall_mem_quotientPointsSubgroup_iff
    {M : Type w₁} [AddCommGroup M] [Module k M] [Comodule k H M]
    (W : Submodule k M) (I : HopfIdeal k H)
    (h : ∀ (A : Type v) [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I
          (CommAlgCat.of k A) ↔
        (W.baseChange A).map (Comodule.endOfPoint M g.ofConv) = W.baseChange A) :
    W.stabilizerHopfIdeal H = I :=
  hopfIdeal_eq_of_forall_quotient_le_ker fun A _ _ g ↦ by
    have hker : (∀ x ∈ I, g.ofConv x = 0) ↔ I.toIdeal ≤ RingHom.ker g.ofConv :=
      ⟨fun hg _ hx ↦ hg _ hx, fun hg _ hx ↦ hg hx⟩
    rw [W.stabilizerHopfIdeal_le_ker_iff g, ← h A g,
      CommHopfAlgCat.mem_quotientPointsSubgroup_iff, hker]

/-- Two subspaces of comodules have the same stabilizer Hopf ideal when every `H`-point in the
universe of `H` stabilizes the scalar extension of one if and only if it stabilizes that of the
other. -/
theorem stabilizerHopfIdeal_eq_of_forall_map_endOfPoint_eq_iff
    {M₁ : Type w₁} {M₂ : Type w₂} [AddCommGroup M₁] [Module k M₁] [Comodule k H M₁]
    [AddCommGroup M₂] [Module k M₂] [Comodule k H M₂]
    (W₁ : Submodule k M₁) (W₂ : Submodule k M₂)
    (h : ∀ (A : Type v) [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)),
      (W₁.baseChange A).map (Comodule.endOfPoint M₁ g.ofConv) = W₁.baseChange A ↔
        (W₂.baseChange A).map (Comodule.endOfPoint M₂ g.ofConv) = W₂.baseChange A) :
    W₁.stabilizerHopfIdeal H = W₂.stabilizerHopfIdeal H :=
  hopfIdeal_eq_of_forall_quotient_le_ker fun A _ _ g ↦ by
    rw [W₁.stabilizerHopfIdeal_le_ker_iff g, W₂.stabilizerHopfIdeal_le_ker_iff g, h A g]

/-- Transporting a comodule along a linear equivalence preserves subspace stabilizer Hopf ideals. -/
theorem stabilizerHopfIdeal_map_transport
    {M : Type w₁} {N : Type w₂} [AddCommGroup M] [Module k M] [Comodule k H M]
    [AddCommGroup N] [Module k N] (e : M ≃ₗ[k] N) (W : Submodule k M) :
    (letI : Comodule k H N := Comodule.Transport (R := k) (C := H) e
     (W.map e.toLinearMap).stabilizerHopfIdeal H) = W.stabilizerHopfIdeal H := by
  let _ : Comodule k H N := Comodule.Transport (R := k) (C := H) e
  refine stabilizerHopfIdeal_eq_of_forall_map_endOfPoint_eq_iff (W.map e.toLinearMap) W
    fun A _ _ g ↦ ?_
  have hcomp : Comodule.endOfPoint N g.ofConv ∘ₗ e.toLinearMap.baseChange A =
      e.toLinearMap.baseChange A ∘ₗ Comodule.endOfPoint M g.ofConv := by
    simpa only [Comodule.transportToHom_toLinearMap] using
      (Comodule.baseChange_comp_endOfPoint
        (Comodule.transportToHom (R := k) (C := H) e) g.ofConv).symm
  have hinj : Function.Injective (e.toLinearMap.baseChange A) :=
    (e.baseChange k A).injective
  rw [Submodule.baseChange_map, ← Submodule.map_comp, hcomp, Submodule.map_comp]
  exact (Submodule.map_injective_of_injective hinj).eq_iff

/-- Over a field, the stabilizer Hopf ideal of the line spanned by a nonzero pure tensor `m ⊗ₜ n` is
the supremum of the line stabilizers of `m` and `n`. -/
theorem stabilizerHopfIdeal_span_singleton_tmul
    {M : Type w₁} {N : Type w₂} [AddCommGroup M] [Module k M] [Comodule k H M]
    [AddCommGroup N] [Module k N] [Comodule k H N]
    {m : M} (hm : m ≠ 0) {n : N} (hn : n ≠ 0) :
    (letI : Comodule k H (M ⊗[k] N) := Comodule.tensor k H M N
     (k ∙ (m ⊗ₜ[k] n)).stabilizerHopfIdeal H) =
      (k ∙ m).stabilizerHopfIdeal H ⊔ (k ∙ n).stabilizerHopfIdeal H := by
  let _ : Comodule k H (M ⊗[k] N) := Comodule.tensor k H M N
  obtain ⟨φ₀, hφ₀⟩ := Module.Projective.exists_dual_eq_one k hm
  obtain ⟨ψ₀, hψ₀⟩ := Module.Projective.exists_dual_eq_one k hn
  refine hopfIdeal_eq_of_forall_quotient_le_ker fun A _ _ g ↦ ?_
  have hmu : Module.IsUnimodular A ((1 : A) ⊗ₜ[k] m) :=
    Module.isUnimodular_of_apply_eq_one (f := Module.Dual.baseChange A φ₀) (by simp [hφ₀])
  have hnu : Module.IsUnimodular A ((1 : A) ⊗ₜ[k] n) :=
    Module.isUnimodular_of_apply_eq_one (f := Module.Dual.baseChange A ψ₀) (by simp [hψ₀])
  rw [HopfIdeal.sup_toIdeal, sup_le_iff, stabilizerHopfIdeal_le_ker_iff,
    stabilizerHopfIdeal_le_ker_iff, stabilizerHopfIdeal_le_ker_iff]
  simp only [Submodule.baseChange_span, Set.image_singleton, TensorProduct.mk_apply,
    Submodule.map_span]
  let d := TensorProduct.AlgebraTensorModule.distribBaseChange k A M N
  have hinj : Function.Injective d.toLinearMap := d.injective
  rw [← (Submodule.map_injective_of_injective hinj).eq_iff]
  simp only [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe]
  have hd1 : d (Comodule.endOfPoint (M ⊗[k] N) g.ofConv (1 ⊗ₜ[k] (m ⊗ₜ[k] n))) =
      Comodule.endOfPoint M g.ofConv (1 ⊗ₜ[k] m) ⊗ₜ[A]
        Comodule.endOfPoint N g.ofConv (1 ⊗ₜ[k] n) := by
    have h := congrArg d (Comodule.endOfPoint_tensor_tmul g.ofConv (1 : A) 1 m n).symm
    simpa [d] using h
  have hd0 : d (1 ⊗ₜ[k] (m ⊗ₜ[k] n)) = (1 ⊗ₜ[k] m) ⊗ₜ[A] (1 ⊗ₜ[k] n) := by simp [d]
  rw [hd1, hd0]
  exact span_singleton_tmul_eq_iff_of_isUnimodular hmu hnu

/-- Over a field, the line spanned by the exterior product of a linearly independent tuple `v` in a
finite-dimensional comodule has the same stabilizer Hopf ideal as `span k (range v)`. -/
theorem stabilizerHopfIdeal_span_ιMulti
    {M : Type w₁} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]
    {d : ℕ} {v : Fin d → M} (hv : LinearIndependent k v) :
    (letI : Comodule k H (⋀[k]^d M) := Comodule.exteriorPower k H M d
     (k ∙ _root_.exteriorPower.ιMulti k d v).stabilizerHopfIdeal H) =
      (Submodule.span k (Set.range v)).stabilizerHopfIdeal H := by
  let W := Submodule.span k (Set.range v)
  have hdimW : Module.finrank k W = d := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  let E := LinearMap.range (_root_.exteriorPower.map d W.subtype)
  have hdimE : Module.finrank k E = 1 := by
    rw [exteriorPower.finrank_range_map W.injective_subtype, hdimW, Nat.choose_self]
  have hmem : _root_.exteriorPower.ιMulti k d v ∈ E :=
    ⟨_root_.exteriorPower.ιMulti k d (fun i ↦ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩),
      _root_.exteriorPower.map_apply_ιMulti W.subtype _⟩
  have hE : k ∙ _root_.exteriorPower.ιMulti k d v = E :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdimE hmem
      ((_root_.exteriorPower.ιMulti_ne_zero_iff v).mpr hv) |>.symm
  let _ : Comodule k H (⋀[k]^d M) := Comodule.exteriorPower k H M d
  rw [hE]
  refine stabilizerHopfIdeal_eq_of_forall_map_endOfPoint_eq_iff E W fun A _ _ g ↦ ?_
  let P (n : ℕ) : Prop :=
    letI : Comodule k H (⋀[k]^n M) := Comodule.exteriorPower k H M n
    ((LinearMap.range (_root_.exteriorPower.map n W.subtype)).baseChange A).map
        (Comodule.endOfPoint (⋀[k]^n M) g.ofConv) =
      (LinearMap.range (_root_.exteriorPower.map n W.subtype)).baseChange A ↔
      (W.baseChange A).map (Comodule.endOfPoint M g.ofConv) = W.baseChange A
  change P d
  exact hdimW ▸ Comodule.map_endOfPoint_baseChange_range_exteriorPowerMap_finrank_eq_iff W A g

end Submodule

end StabilizerLemmas

namespace TauCeti.Comodule

section FlagStabilizer

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
  [Field k] [CommRing H] [HopfAlgebra k H] [AddCommGroup M] [Module k M] [Comodule k H M]

/-- For a linearly independent tuple `v : Fin d → M` in a finite-dimensional comodule, the line
stabilizer of `exteriorFlagVector k d v` is the supremum of the stabilizers of its prefix spans. -/
theorem stabilizerHopfIdeal_span_exteriorFlagVector_of_linearIndependent [Module.Finite k M]
    {d : ℕ} {v : Fin d → M} (hv : LinearIndependent k v) :
    (letI : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
     (k ∙ exteriorPower.exteriorFlagVector k d v).stabilizerHopfIdeal H) =
      Finset.univ.sup fun r : Fin (d + 1) ↦
        (Submodule.span k (Set.range (v ∘ Fin.castLE (Nat.le_of_lt_succ r.2)))).stabilizerHopfIdeal
          H := by
  induction d with
  | zero =>
    let _ : Comodule k H (⋀[k]^0 M) := exteriorPower k H M 0
    have hmap : (k ∙ _root_.exteriorPower.ιMulti k 0 v).map
        (exteriorPower.flagSpaceZeroEquiv k M).symm.toLinearMap =
        k ∙ exteriorPower.exteriorFlagVector k 0 v := by
      rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe,
        ← exteriorPower.exteriorFlagVector_zero]
    change (letI : Comodule k H (exteriorPower.FlagSpace k M 0) :=
        Transport (exteriorPower.flagSpaceZeroEquiv k M).symm
      (k ∙ exteriorPower.exteriorFlagVector k 0 v).stabilizerHopfIdeal H) = _
    rw [← hmap, Submodule.stabilizerHopfIdeal_map_transport,
      Submodule.stabilizerHopfIdeal_span_ιMulti hv]
    let f0 : Fin 1 → HopfIdeal k H := fun r ↦
      (Submodule.span k (Set.range (v ∘ Fin.castLE (Nat.le_of_lt_succ r.2)))).stabilizerHopfIdeal H
    have hf0 : (Submodule.span k (Set.range v)).stabilizerHopfIdeal H = f0 0 := rfl
    rw [hf0]
    exact le_antisymm (Finset.le_sup (f := f0) (Finset.mem_univ 0))
      (Finset.sup_le fun r _ ↦ by rw [Fin.eq_zero r])
  | succ r ih =>
    let _ : Comodule k H (exteriorPower.FlagSpace k M r) := exteriorFlag k H M r
    let _ : Comodule k H (⋀[k]^(r + 1) M) := exteriorPower k H M (r + 1)
    let _ : Comodule k H (exteriorPower.FlagSpace k M r ⊗[k] ⋀[k]^(r + 1) M) :=
      tensor k H (exteriorPower.FlagSpace k M r) (⋀[k]^(r + 1) M)
    have hv' : LinearIndependent k (v ∘ Fin.castSucc) := hv.comp _ (Fin.castSucc_injective r)
    have hx : exteriorPower.exteriorFlagVector k r (v ∘ Fin.castSucc) ≠ 0 :=
      (exteriorPower.exteriorFlagVector_ne_zero_iff (v := v ∘ Fin.castSucc)).mpr hv'
    have hy : _root_.exteriorPower.ιMulti k (r + 1) v ≠ 0 :=
      (_root_.exteriorPower.ιMulti_ne_zero_iff v).mpr hv
    have hmap : (k ∙ (exteriorPower.exteriorFlagVector k r (v ∘ Fin.castSucc) ⊗ₜ[k]
          _root_.exteriorPower.ιMulti k (r + 1) v)).map
        (exteriorPower.flagSpaceSuccEquiv k M r).symm.toLinearMap =
        k ∙ exteriorPower.exteriorFlagVector k (r + 1) v := by
      rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe,
        ← exteriorPower.exteriorFlagVector_succ]
    change (letI : Comodule k H (exteriorPower.FlagSpace k M (r + 1)) :=
        Transport (exteriorPower.flagSpaceSuccEquiv k M r).symm
      (k ∙ exteriorPower.exteriorFlagVector k (r + 1) v).stabilizerHopfIdeal H) = _
    rw [← hmap, Submodule.stabilizerHopfIdeal_map_transport,
      Submodule.stabilizerHopfIdeal_span_singleton_tmul hx hy, ih hv',
      Submodule.stabilizerHopfIdeal_span_ιMulti hv]
    let g : Fin (r + 2) → HopfIdeal k H := fun j ↦
      (Submodule.span k (Set.range (v ∘ Fin.castLE (Nat.le_of_lt_succ j.2)))).stabilizerHopfIdeal H
    have hcast (j : Fin (r + 1)) :
        (Submodule.span k
          (Set.range ((v ∘ Fin.castSucc) ∘ Fin.castLE (Nat.le_of_lt_succ j.2)))).stabilizerHopfIdeal
          H = g j.castSucc := rfl
    have hlast : (Submodule.span k (Set.range v)).stabilizerHopfIdeal H = g (Fin.last (r + 1)) := by
      have hv_eq : v = v ∘ Fin.castLE (Nat.le_of_lt_succ (Fin.last (r + 1)).2) := rfl
      exact congrArg (fun u ↦ (Submodule.span k (Set.range u)).stabilizerHopfIdeal H) hv_eq
    refine le_antisymm (sup_le ?_ ?_) (Finset.sup_le fun idx _ ↦ ?_)
    · refine Finset.sup_le fun j _ ↦ ?_
      rw [hcast j]
      exact Finset.le_sup (f := g) (Finset.mem_univ j.castSucc)
    · rw [hlast]
      exact Finset.le_sup (f := g) (Finset.mem_univ (Fin.last (r + 1)))
    · refine idx.lastCases (hlast ▸ le_sup_right) fun j ↦ ?_
      let f' : Fin (r + 1) → HopfIdeal k H := fun j ↦
        (Submodule.span k
          (Set.range ((v ∘ Fin.castSucc) ∘ Fin.castLE (Nat.le_of_lt_succ j.2)))).stabilizerHopfIdeal
          H
      have hj : g j.castSucc = f' j := (hcast j).symm
      exact le_sup_of_le_left (hj.trans_le (Finset.le_sup (f := f') (Finset.mem_univ j)))

/-- For a basis `b : Module.Basis (Fin d) k M`, the line stabilizer of `exteriorFlagVector k d b` is
the supremum of the stabilizers of all steps `b.flag r` of the basis flag. -/
theorem stabilizerHopfIdeal_span_exteriorFlagVector {d : ℕ} (b : Module.Basis (Fin d) k M) :
    (letI : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
     (k ∙ exteriorPower.exteriorFlagVector k d b).stabilizerHopfIdeal H) =
      Finset.univ.sup fun r : Fin (d + 1) ↦ (b.flag r).stabilizerHopfIdeal H := by
  have : Module.Finite k M := Module.Finite.of_basis b
  rw [stabilizerHopfIdeal_span_exteriorFlagVector_of_linearIndependent b.linearIndependent]
  refine Finset.sup_congr rfl fun r _ ↦ ?_
  have hset : Set.range (b ∘ Fin.castLE (Nat.le_of_lt_succ r.2)) =
      b '' {i : Fin d | i.castSucc < r} := by
    ext x
    simp only [Set.mem_range, Function.comp_apply, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.castLE (Nat.le_of_lt_succ r.2) i, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.val, hi⟩, rfl⟩
  rw [Module.Basis.flag, hset]

/-- A subspace `W` of an `H`-comodule `M` has stabilizer Hopf ideal at most `J` if and only if `W`
is the underlying submodule of an `(H ⧸ J.toIdeal)`-subcomodule under corestriction. -/
theorem stabilizerHopfIdeal_le_iff_exists_subcomodule_corestrict
    (W : Submodule k M) (J : HopfIdeal k H) :
    W.stabilizerHopfIdeal H ≤ J ↔
      (letI : Comodule k (H ⧸ J.toIdeal) M :=
        Corestrict (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) J).hom.toCoalgHom
       ∃ N : Subcomodule k (H ⧸ J.toIdeal) M, N.toSubmodule = W) := by
  let q := (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) J).hom
  let _ : Comodule k (H ⧸ J.toIdeal) M := Corestrict q.toCoalgHom
  have hbot : W.stabilizerHopfIdeal H ≤ J ↔ W.stabilizerHopfIdeal (H ⧸ J.toIdeal) = ⊥ := by
    rw [Submodule.stabilizerHopfIdeal_le_iff, eq_bot_iff, Submodule.stabilizerHopfIdeal_le_iff]
    refine forall_congr' fun ψ ↦ forall₂_congr fun w _ ↦ ?_
    rw [CoalgHom.matrixCoefficient_corestrict, HopfIdeal.mem_bot]
    exact (CommHopfAlgCat.mkQuotient_eq_zero_iff (_root_.CommHopfAlgCat.of k H) J _).symm
  rw [hbot, Submodule.stabilizerHopfIdeal_eq_bot_iff]
  exact ⟨fun h ↦ ⟨Subcomodule.ofSubmodule W h, rfl⟩,
    by rintro ⟨N, rfl⟩ w hw; exact N.coact_mem hw⟩

/-- The line stabilizer of `exteriorFlagVector k d b` lies below `J` if and only if the corestricted
coefficient matrix of `b` over `H ⧸ J.toIdeal` is upper triangular. -/
theorem stabilizerHopfIdeal_span_exteriorFlagVector_le_iff {d : ℕ} (b : Module.Basis (Fin d) k M)
    (J : HopfIdeal k H) :
    (letI : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
     (k ∙ exteriorPower.exteriorFlagVector k d b).stabilizerHopfIdeal H) ≤ J ↔
      (letI : Comodule k (H ⧸ J.toIdeal) M :=
        Corestrict (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) J).hom.toCoalgHom
       (coefficientMatrix (C := H ⧸ J.toIdeal) b).IsUpperTriangular) := by
  let _ : Comodule k (H ⧸ J.toIdeal) M :=
    Corestrict (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) J).hom.toCoalgHom
  rw [stabilizerHopfIdeal_span_exteriorFlagVector, Finset.sup_le_iff,
    coefficientMatrix_isUpperTriangular_iff (C := H ⧸ J.toIdeal) b]
  exact ⟨fun h r ↦ (stabilizerHopfIdeal_le_iff_exists_subcomodule_corestrict (b.flag r) J).mp
      (h r (Finset.mem_univ r)),
    fun h r _ ↦
      (stabilizerHopfIdeal_le_iff_exists_subcomodule_corestrict (b.flag r) J).mpr (h r)⟩

/-- If `b : Module.Basis (Fin (1 + n)) k M` has upper-triangular coefficient matrix over
`H ⧸ J.toIdeal` and its first line `k ∙ b 0` has stabilizer `J`, then the exterior flag vector of
`b` also has line stabilizer `J`. -/
theorem stabilizerHopfIdeal_span_exteriorFlagVector_eq {n : ℕ}
    (b : Module.Basis (Fin (1 + n)) k M) (J : HopfIdeal k H)
    (h0 : (k ∙ b 0).stabilizerHopfIdeal H = J)
    (htri : letI : Comodule k (H ⧸ J.toIdeal) M :=
        Corestrict (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) J).hom.toCoalgHom
      (coefficientMatrix (C := H ⧸ J.toIdeal) b).IsUpperTriangular) :
    (letI : Comodule k H (exteriorPower.FlagSpace k M (1 + n)) := exteriorFlag k H M (1 + n)
     (k ∙ exteriorPower.exteriorFlagVector k (1 + n) b).stabilizerHopfIdeal H) = J := by
  refine le_antisymm ((stabilizerHopfIdeal_span_exteriorFlagVector_le_iff b J).mpr htri) ?_
  rw [stabilizerHopfIdeal_span_exteriorFlagVector, ← h0]
  have hflag1 : b.flag (Fin.succ (0 : Fin (1 + n))) = k ∙ b 0 := by
    rw [b.flag_succ, Fin.castSucc_zero, b.flag_zero, sup_bot_eq]
  rw [← hflag1]
  exact Finset.le_sup (f := fun r : Fin (1 + n + 1) ↦ (b.flag r).stabilizerHopfIdeal H)
    (Finset.mem_univ (Fin.succ 0))

/-- If `M` contains a subspace `W₀` whose stabilizer `J` has solvable `k`-points, then for *every*
basis `b : Module.Basis (Fin d) k M` the `k`-points of the quotient by the line stabilizer of
`exteriorFlagVector k d b` form a solvable group. -/
theorem isSolvable_points_quotient_stabilizerHopfIdeal_exteriorFlagVector
    {d : ℕ} (b : Module.Basis (Fin d) k M) {W₀ : Submodule k M} {J : HopfIdeal k H}
    (hW₀ : W₀.stabilizerHopfIdeal H = J)
    [Group.IsSolvable (WithConv ((H ⧸ J.toIdeal) →ₐ[k] k))] :
    letI : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
    let D := (k ∙ exteriorPower.exteriorFlagVector k d b).stabilizerHopfIdeal H
    Group.IsSolvable (WithConv ((H ⧸ D.toIdeal) →ₐ[k] k)) := by
  let _ : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
  set D := (k ∙ exteriorPower.exteriorFlagVector k d b).stabilizerHopfIdeal H
  let Hcat := _root_.CommHopfAlgCat.of k H
  let ιD := (CommHopfAlgCat.quotientPointsHom Hcat D (CommAlgCat.of k k)).hom
  let ιJ := (CommHopfAlgCat.quotientPointsHom Hcat J (CommAlgCat.of k k)).hom
  let eMat : (Module.End k M)ˣ ≃* Matrix.GeneralLinearGroup (Fin d) k :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  let ρ : WithConv (H →ₐ[k] k) →* Matrix.GeneralLinearGroup (Fin d) k :=
    eMat.toMonoidHom.comp
      (Representation.asGroupHom (basePointsRepresentation (R := k) (H := H) M))
  let f := ρ.comp ιD
  have hf_mem (g : WithConv ((H ⧸ D.toIdeal) →ₐ[k] k)) :
      f g ∈ upperTriangularGroup (Fin d) k := by
    have hgD : ιD g ∈ CommHopfAlgCat.quotientPointsSubgroup Hcat D (CommAlgCat.of k k) := ⟨g, rfl⟩
    have hstab := (Submodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff
      (k ∙ exteriorPower.exteriorFlagVector k d b) (ιD g)).mp hgD
    let α : M ≃ₗ[k] M := LinearMap.GeneralLinearGroup.generalLinearEquiv k M
      (Representation.asGroupHom (basePointsRepresentation (R := k) (H := H) M) (ιD g))
    have hα : exteriorPower.exteriorFlagMap d α.toLinearMap
        (exteriorPower.exteriorFlagVector k d b) ∈ k ∙ exteriorPower.exteriorFlagVector k d b := by
      have hmem : basePointsRepresentation (exteriorPower.FlagSpace k M d) (ιD g)
          (exteriorPower.exteriorFlagVector k d b) ∈ k ∙ exteriorPower.exteriorFlagVector k d b :=
        hstab ▸ Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
      rwa [basePointsRepresentation_exteriorFlag] at hmem
    exact UpperTriangularGroup.mem_iff.mpr
      (exteriorPower.isUpperTriangular_toMatrix_of_exteriorFlagMap_mem_span b α hα)
  let f_tri : WithConv ((H ⧸ D.toIdeal) →ₐ[k] k) →* upperTriangularGroup (Fin d) k :=
    f.codRestrict (upperTriangularGroup (Fin d) k) hf_mem
  have hker_mem (g : f.ker) :
      ιD g.1 ∈ CommHopfAlgCat.quotientPointsSubgroup Hcat J (CommAlgCat.of k k) := by
    have h1 : Representation.asGroupHom (basePointsRepresentation (R := k) (H := H) M)
        (ιD g.1) = 1 :=
      eMat.injective (g.2.trans (map_one eMat).symm)
    have hid : basePointsRepresentation (R := k) (H := H) M (ιD g.1) = LinearMap.id :=
      congrArg Units.val h1
    rw [← hW₀, Submodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff, hid, Submodule.map_id]
  let k_to_J : f.ker →* ιJ.range :=
    (ιD.comp f.ker.subtype).codRestrict ιJ.range hker_mem
  have hk_inj : Function.Injective k_to_J := fun x y hxy ↦
    Subtype.ext ((CommHopfAlgCat.quotientPointsHom_injective Hcat D (CommAlgCat.of k k))
      (congrArg Subtype.val hxy))
  have : Group.IsSolvable ιJ.range := Group.isSolvable_of_surjective ιJ.rangeRestrict_surjective
  have : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hk_inj
  refine Group.isSolvable_of_ker_le_range f.ker.subtype f_tri ?_
  rw [Subgroup.subtype_range, MonoidHom.ker_codRestrict]

end FlagStabilizer

end TauCeti.Comodule

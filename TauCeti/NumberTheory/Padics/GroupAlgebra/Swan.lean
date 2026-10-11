/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.GroupAlgebra.Rational
import TauCeti.Algebra.Module.Projective.Reduction
import TauCeti.Algebra.Module.Projective.Trans
import TauCeti.Algebra.MonoidAlgebra.CosetBasis
import TauCeti.Algebra.MonoidAlgebra.ProjectiveTrace
import TauCeti.NumberTheory.Padics.GroupAlgebra.Invariants
import TauCeti.NumberTheory.Padics.GroupAlgebra.Projective
import TauCeti.NumberTheory.Padics.GroupAlgebra.Reduction
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.LinHom.Basic
import TauCeti.RepresentationTheory.OfModule
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Jacobson.Semiprimary
import TauCeti.RingTheory.Semisimple.Multiplicity

/-!
# Swan's theorem for `ℤ_p[G]`

For a finite group `G`, two finitely generated projective `ℤ_p[G]`-modules are isomorphic when
their rationalizations are isomorphic. This is Swan's theorem, NSW (5.6.10)(ii).

The proof first detects the reductions modulo `p` by counting maps to every simple
`𝔽_p[G]`-module. Those counts are dimensions of invariant spaces in conjugation
representations. Projective lifts turn the dimensions into integral invariant ranks, which the
character formula computes from traces. Traces at `p`-singular elements vanish for projective
modules. For a `p`-regular element, restriction to its cyclic subgroup reduces trace equality to
the prime-to-`p` case of Swan's theorem. The resulting equivalence modulo `p` lifts to an
integral equivalence because both modules are projective.

## Main result

* `TauCeti.nonempty_linearEquiv_of_projective_of_tensorRat`: finitely generated projective
  `ℤ_p[G]`-modules with isomorphic rationalizations are isomorphic.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Proposition (5.6.10)(ii).
* R. G. Swan, *Induced representations and projective modules*, Ann. of Math. 71 (1960).
-/

public section

open scoped TensorProduct Pointwise MonoidAlgebra
namespace TauCeti

universe u v w

/-- **Swan's theorem for `ℤ_p[G]`** (NSW (5.6.10)(ii)). Two finitely generated projective
`ℤ_p[G]`-modules with isomorphic rationalizations are isomorphic. -/
theorem nonempty_linearEquiv_of_projective_of_tensorRat
    (p : ℕ) [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module ℤ_[p] M]
    [Module (MonoidAlgebra ℤ_[p] G) M]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) M]
    [Module.Finite (MonoidAlgebra ℤ_[p] G) M]
    [Module.Projective (MonoidAlgebra ℤ_[p] G) M]
    [AddCommGroup N] [Module ℤ_[p] N] [Module (MonoidAlgebra ℤ_[p] G) N]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) N]
    [Module.Finite (MonoidAlgebra ℤ_[p] G) N]
    [Module.Projective (MonoidAlgebra ℤ_[p] G) N]
    (h : Nonempty ((M ⊗[ℤ_[p]] ℚ_[p]) ≃ₗ[MonoidAlgebra ℤ_[p] G]
      (N ⊗[ℤ_[p]] ℚ_[p]))) :
    Nonempty (M ≃ₗ[MonoidAlgebra ℤ_[p] G] N) := by
  classical
  let A := MonoidAlgebra ℤ_[p] G
  let kG := MonoidAlgebra (ZMod p) G
  let I := Ideal.span {(p : A)}
  let M₀ := M ⧸ I • (⊤ : Submodule A M)
  let N₀ := N ⧸ I • (⊤ : Submodule A N)
  let _ : Module kG M₀ := padicReductionModule p G M
  let _ : Module kG N₀ := padicReductionModule p G N
  let _ : Module.Finite kG M₀ := padicReduction_module_finite p G M
  let _ : Module.Finite kG N₀ := padicReduction_module_finite p G N
  let _ : Module.Projective kG M₀ := padicReduction_module_projective p G M
  let _ : Module.Projective kG N₀ := padicReduction_module_projective p G N
  let _ : Finite (G →₀ ZMod p) := Finite.of_injective _ DFunLike.coe_injective
  let _ : Finite kG := Finite.of_injective _ MonoidAlgebra.coeff_injective
  let _ : Finite (kG ⧸ Ring.jacobson kG) :=
    Finite.of_surjective (Ideal.Quotient.mk (Ring.jacobson kG))
      Ideal.Quotient.mk_surjective
  have hred : Nonempty (M₀ ≃ₗ[kG] N₀) := by
    apply nonempty_linearEquiv_of_projective_of_natCard_linearMap_eq M₀ N₀
    intro S _ _ _
    let _ : Finite S := IsSimpleModule.finite_of_finite_quotient_jacobson (R := kG) S
    let _ : Module (ZMod p) M₀ := Module.compHom M₀ (algebraMap (ZMod p) kG)
    let _ : Module (ZMod p) N₀ := Module.compHom N₀ (algebraMap (ZMod p) kG)
    let _ : Module (ZMod p) S := Module.compHom S (algebraMap (ZMod p) kG)
    let _ : IsScalarTower (ZMod p) kG M₀ := IsScalarTower.of_compHom (ZMod p) kG M₀
    let _ : IsScalarTower (ZMod p) kG N₀ := IsScalarTower.of_compHom (ZMod p) kG N₀
    let _ : IsScalarTower (ZMod p) kG S := IsScalarTower.of_compHom (ZMod p) kG S
    let _ : Module.Finite (ZMod p) M₀ := .trans kG M₀
    let _ : Module.Finite (ZMod p) N₀ := .trans kG N₀
    let _ : Module.Finite (ZMod p) S := inferInstance
    let ρM := Representation.ofModule' (k := ZMod p) (G := G) M₀
    let ρN := Representation.ofModule' (k := ZMod p) (G := G) N₀
    let σ := Representation.ofModule' (k := ZMod p) (G := G) S
    let eM : ρM.asModule ≃ₗ[kG] M₀ :=
      TauCeti.Representation.ofModule'AsModuleEquiv (k := ZMod p) (G := G) M₀
    let eN : ρN.asModule ≃ₗ[kG] N₀ :=
      TauCeti.Representation.ofModule'AsModuleEquiv (k := ZMod p) (G := G) N₀
    let eS : σ.asModule ≃ₗ[kG] S :=
      TauCeti.Representation.ofModule'AsModuleEquiv (k := ZMod p) (G := G) S
    let _ : Module.Finite kG ρM.asModule := Module.Finite.equiv eM.symm
    let _ : Module.Finite kG ρN.asModule := Module.Finite.equiv eN.symm
    let _ : Module.Projective kG ρM.asModule := Module.Projective.of_equiv' eM.symm
    let _ : Module.Projective kG ρN.asModule := Module.Projective.of_equiv' eN.symm
    -- The Hom spaces into `S` are the invariants of the Hom representations `YM` and `YN`.
    let YM := Representation.linHom ρM σ
    let YN := Representation.linHom ρN σ
    rw [← Nat.card_congr (((Representation.invariantsEquivIntertwiningMap ρM σ).trans
        (Representation.IntertwiningMap.equivLinearMapAsModule ρM σ)).toAddEquiv.trans
          (eM.arrowCongrAddEquiv eS)).toEquiv,
      ← Nat.card_congr (((Representation.invariantsEquivIntertwiningMap ρN σ).trans
        (Representation.IntertwiningMap.equivLinearMapAsModule ρN σ)).toAddEquiv.trans
          (eN.arrowCongrAddEquiv eS)).toEquiv]
    -- Lift `YM` and `YN` to projective `ℤ_p[G]`-modules `XM` and `XN`, and count invariants.
    obtain ⟨_, XM, hXMf, hXMp, fM, hfM⟩ :=
      exists_projective_reduction_bijective_of_projective p G YM.asModule
    obtain ⟨_, XN, hXNf, hXNp, fN, hfN⟩ :=
      exists_projective_reduction_bijective_of_projective p G YN.asModule
    let _ : Module.Finite A XM := hXMf
    let _ : Module.Projective A XM := hXMp
    let _ : Module.Finite A XN := hXNf
    let _ : Module.Projective A XN := hXNp
    let _ : Module.Finite ℤ_[p] XM := .trans A XM
    let _ : Module.Finite ℤ_[p] XN := .trans A XN
    let _ : Module.Projective ℤ_[p] XM := Module.Projective.trans (S := A)
    let _ : Module.Projective ℤ_[p] XN := Module.Projective.trans (S := A)
    let ξM := Representation.ofModule' (k := ℤ_[p]) (G := G) XM
    let ξN := Representation.ofModule' (k := ℤ_[p]) (G := G) XN
    rw [Representation.natCard_invariants_eq_pow_finrank_of_bijective p YM XM fM hfM,
      Representation.natCard_invariants_eq_pow_finrank_of_bijective p YN XN fN hfN]
    -- The invariant ranks are computed rationally by the average of the characters.
    congr 1
    rw [← Representation.finrank_invariants_baseChange_ratPadic p ξM,
      ← Representation.finrank_invariants_baseChange_ratPadic p ξN]
    let _ := Fintype.ofFinite G
    let _ : Invertible (Nat.card G : ℚ_[p]) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    apply Nat.cast_injective (R := ℚ_[p])
    rw [← (Representation.baseChange ℚ_[p] ξM).card_inv_mul_sum_char_eq_finrank,
      ← (Representation.baseChange ℚ_[p] ξN).card_inv_mul_sum_char_eq_finrank]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    simp only [Representation.character, Representation.baseChange_apply,
      LinearMap.trace_baseChange]
    congr 1
    by_cases hg : p ∣ orderOf g
    · rw [trace_ofModule'_eq_zero_of_dvd_orderOf XM (p := p)
          (show ¬IsUnit (p : ℤ_[p]) by exact PadicInt.p_nonunit) hg,
        trace_ofModule'_eq_zero_of_dvd_orderOf XN (p := p)
          (show ¬IsUnit (p : ℤ_[p]) by exact PadicInt.p_nonunit) hg]
    -- For `p`-regular `g`, restrict to `C = ⟨g⟩`, whose order is prime to `p`.
    let C := Subgroup.zpowers g
    let AC := MonoidAlgebra ℤ_[p] C
    let kC := MonoidAlgebra (ZMod p) C
    let φA : AC →ₐ[ℤ_[p]] A := MonoidAlgebra.mapDomainAlgHom ℤ_[p] ℤ_[p] C.subtype
    let φk : kC →ₐ[ZMod p] kG := MonoidAlgebra.mapDomainAlgHom (ZMod p) (ZMod p) C.subtype
    let _ : Module AC A := (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype).toModule
    have : IsScalarTower AC A A := ⟨fun r s t ↦ mul_assoc (φA r) s t⟩
    let b := TauCeti.MonoidAlgebra.basisCosets ℤ_[p] C.subtype C.subtype_injective
    have : Module.Free AC A := .of_basis b
    have : Module.Finite AC A := .of_basis b
    -- Restrict scalars of `M`, `N`, `XM` and `XN` to `ℤ_p[C]`.
    let _ : Module AC M := .compHom M (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype)
    let _ : Module AC N := .compHom N (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype)
    let _ : Module AC XM := .compHom XM (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype)
    let _ : Module AC XN := .compHom XN (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype)
    have : IsScalarTower AC A M := ⟨fun r s x ↦ mul_smul (φA r) s x⟩
    have : IsScalarTower AC A N := ⟨fun r s x ↦ mul_smul (φA r) s x⟩
    have : IsScalarTower AC A XM := ⟨fun r s x ↦ mul_smul (φA r) s x⟩
    have : IsScalarTower AC A XN := ⟨fun r s x ↦ mul_smul (φA r) s x⟩
    have : IsScalarTower ℤ_[p] AC M :=
      ⟨fun a r x ↦ (congrArg (· • x) (map_smul φA a r)).trans (smul_assoc a (φA r) x)⟩
    have : IsScalarTower ℤ_[p] AC N :=
      ⟨fun a r x ↦ (congrArg (· • x) (map_smul φA a r)).trans (smul_assoc a (φA r) x)⟩
    have : IsScalarTower ℤ_[p] AC XM :=
      ⟨fun a r x ↦ (congrArg (· • x) (map_smul φA a r)).trans (smul_assoc a (φA r) x)⟩
    have : IsScalarTower ℤ_[p] AC XN :=
      ⟨fun a r x ↦ (congrArg (· • x) (map_smul φA a r)).trans (smul_assoc a (φA r) x)⟩
    have : Module.Finite AC M := .trans A M
    have : Module.Finite AC N := .trans A N
    have : Module.Finite AC XM := .trans A XM
    have : Module.Finite AC XN := .trans A XN
    have : Module.Projective AC M := .trans (S := A)
    have : Module.Projective AC N := .trans (S := A)
    have : Module.Projective AC XM := .trans (S := A)
    have : Module.Projective AC XN := .trans (S := A)
    -- Swan's theorem for `C` identifies `M` and `N` over `ℤ_p[C]`, hence `M₀` and `N₀`.
    obtain ⟨eMN⟩ := nonempty_linearEquiv_of_projective_of_tensorRat_of_not_dvd p
      (by simpa only [C, Nat.card_zpowers] using hg) M N
      (h.map fun e ↦ e.restrictScalars AC)
    let _ : Module kC M₀ := .compHom M₀ (MonoidAlgebra.mapDomainRingHom (ZMod p) C.subtype)
    let _ : Module kC N₀ := .compHom N₀ (MonoidAlgebra.mapDomainRingHom (ZMod p) C.subtype)
    let _ : Module kC S := .compHom S (MonoidAlgebra.mapDomainRingHom (ZMod p) C.subtype)
    have : IsScalarTower (ZMod p) kC M₀ :=
      ⟨fun a r x ↦ (congrArg (· • x) (map_smul φk a r)).trans (smul_assoc a (φk r) x)⟩
    have : IsScalarTower (ZMod p) kC N₀ :=
      ⟨fun a r x ↦ (congrArg (· • x) (map_smul φk a r)).trans (smul_assoc a (φk r) x)⟩
    have : IsScalarTower (ZMod p) kC S :=
      ⟨fun a r x ↦ (congrArg (· • x) (map_smul φk a r)).trans (smul_assoc a (φk r) x)⟩
    let _ : Module kC (M ⧸ Ideal.span {(p : AC)} • (⊤ : Submodule AC M)) :=
      padicReductionModule p C M
    let _ : Module kC (N ⧸ Ideal.span {(p : AC)} • (⊤ : Submodule AC N)) :=
      padicReductionModule p C N
    let eMN₀ : M₀ ≃ₗ[kC] N₀ :=
      (padicReductionRestrictLinearEquiv p C C.subtype M (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)).symm.trans
        ((padicReductionCongr p C eMN).trans
          (padicReductionRestrictLinearEquiv p C C.subtype N (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)))
    have hφk (c : C) : φk (MonoidAlgebra.single c 1) = MonoidAlgebra.single (c : G) 1 := by
      rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]
      rfl
    have heMN₀ (c : C) (x : M₀) : eMN₀ (ρM c x) = ρN c (eMN₀ x) := by
      rw [TauCeti.Representation.ofModule'_apply, TauCeti.Representation.ofModule'_apply,
        ← hφk]
      -- `k[C]` acts on `M₀` and `N₀` through `φk`.
      exact eMN₀.map_smul (MonoidAlgebra.single c 1) x
    -- Precomposition with `eMN₀` identifies the restrictions of `YM` and `YN` to `C`.
    let YMC : Representation (ZMod p) C (M₀ →ₗ[ZMod p] S) := YM.comp C.subtype
    let YNC : Representation (ZMod p) C (N₀ →ₗ[ZMod p] S) := YN.comp C.subtype
    let ePre : (M₀ →ₗ[ZMod p] S) ≃ₗ[ZMod p] (N₀ →ₗ[ZMod p] S) :=
      LinearEquiv.congrLeft S (ZMod p) (eMN₀.restrictScalars (ZMod p))
    let eY : YMC.Equiv YNC := .mk ePre (by
      intro c
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro x
      simp only [YMC, YNC, YM, YN, ePre, LinearMap.comp_apply, MonoidHom.coe_comp,
        Function.comp_apply, LinearEquiv.congrLeft_apply, AddEquiv.toFun_eq_coe,
        LinearEquiv.arrowCongrAddEquiv_apply, Representation.linHom_apply,
        LinearEquiv.coe_coe, LinearEquiv.refl_apply, Subgroup.coe_subtype,
        LinearEquiv.restrictScalars_symm_apply]
      apply congrArg (σ c)
      apply congrArg f
      apply eMN₀.injective
      rw [← Subgroup.coe_inv, heMN₀, eMN₀.apply_symm_apply, eMN₀.apply_symm_apply])
    -- Transport `eY` through the lifts to an isomorphism of the reductions of `XM` and `XN`
    -- over `C`, and lift that to `ℤ_p[C]`.
    let QXM := XM ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A XM)
    let QXN := XN ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A XN)
    let _ : Module kG QXM := padicReductionModule p G XM
    let _ : Module kG QXN := padicReductionModule p G XN
    let _ : Module kC QXM := .compHom QXM (MonoidAlgebra.mapDomainRingHom (ZMod p) C.subtype)
    let _ : Module kC QXN := .compHom QXN (MonoidAlgebra.mapDomainRingHom (ZMod p) C.subtype)
    let _ : Module kC (XM ⧸ Ideal.span {(p : AC)} • (⊤ : Submodule AC XM)) :=
      padicReductionModule p C XM
    let _ : Module kC (XN ⧸ Ideal.span {(p : AC)} • (⊤ : Submodule AC XN)) :=
      padicReductionModule p C XN
    let eLiftM : QXM ≃ₗ[kC] YMC.asModule := YM.linearEquivAsModuleComp C.subtype
      (fun _ _ ↦ rfl) (padicReductionLinearEquivOfBijective p G fM hfM)
    let eLiftN : QXN ≃ₗ[kC] YNC.asModule := YN.linearEquivAsModuleComp C.subtype
      (fun _ _ ↦ rfl) (padicReductionLinearEquivOfBijective p G fN hfN)
    let eRedC := (padicReductionRestrictLinearEquiv p C C.subtype XM (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl)).trans (eLiftM.trans
        ((TauCeti.Representation.asModuleLinearEquivOfEquiv eY).trans (eLiftN.symm.trans
          (padicReductionRestrictLinearEquiv p C C.subtype XN (fun _ _ ↦ rfl)
            (fun _ _ ↦ rfl)).symm)))
    have := padicReduction_compatibleSMul_padicInt p C (padicReduction_smul p C XM)
      (padicReduction_smul p C XN)
    obtain ⟨eX⟩ := nonempty_linearEquiv_of_projective_of_reduction p C XM XN
      ⟨eRedC.restrictScalars AC⟩
    -- The `ℤ_p[C]`-linear isomorphism `eX` conjugates the action of `g ∈ C`.
    have hφA : φA (MonoidAlgebra.single ⟨g, Subgroup.mem_zpowers g⟩ 1) =
        MonoidAlgebra.single g 1 := by
      rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]
      rfl
    have hconj : (eX.restrictScalars ℤ_[p]).conj (Representation.ofModule' XM g) =
        Representation.ofModule' XN g := LinearMap.ext fun x ↦ by
      rw [LinearEquiv.conj_apply_apply, TauCeti.Representation.ofModule'_apply,
        TauCeti.Representation.ofModule'_apply, ← hφA, LinearEquiv.restrictScalars_apply,
        LinearEquiv.restrictScalars_symm_apply]
      -- `ℤ_p[C]` acts on `XM` and `XN` through `φA`.
      exact (eX.map_smul _ _).trans (congrArg _ (eX.apply_symm_apply x))
    rw [← hconj, LinearMap.trace_conj']
  obtain ⟨ered⟩ := hred
  have := padicReduction_compatibleSMul_padicInt p G (padicReduction_smul p G M)
    (padicReduction_smul p G N)
  exact nonempty_linearEquiv_of_projective_of_reduction p G M N ⟨ered.restrictScalars A⟩

end TauCeti

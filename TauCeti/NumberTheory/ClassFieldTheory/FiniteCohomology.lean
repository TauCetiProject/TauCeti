/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.NumberTheory.ClassFieldTheory.ClassField
public import TauCeti.NumberTheory.ClassFieldTheory.MuNRep
public import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Finiteness
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Finiteness of `H⁰` and `H¹` of a finite Galois module over a local field

Let `F` be a nonarchimedean local field, `n` a natural number invertible in `F`, and `A` a finite
smooth discrete `G_F`-module killed by `n`, an object of `TauCeti.ClassFieldTheory.GalRep n F`.
This file proves that the continuous cohomology groups `H⁰(G_F, A)` and `H¹(G_F, A)` are finite
(`TauCeti.ClassFieldTheory.finite_continuousCohomology_of_le_one`).

The proof chooses a finite Galois extension `L/F` inside `Fˢ` that contains a primitive `n`th root
of unity and over which `A` becomes a trivial module: the class field
`TauCeti.ClassFieldTheory.classField F W` of an open normal subgroup `W` of `Gal(Fˢ/F)` contained
in the kernel of the action and in the stabilizer of the root of unity. The reduction
`TauCeti.ContinuousCohomology.finite_continuousCohomology_of_isOpen_of_normal_of_prime`, through
coinduction from the subgroup `Gal(Fˢ/L) ≅ G_L` and dévissage, leaves the trivial `G_L`-modules
of prime order `ℓ ∣ n`. Such a module is `μ_ℓ(Lˢ)`, because `L` contains the `ℓ`th roots of
unity, and the Kummer isomorphism `TauCeti.kummerIso` identifies `H¹(G_L, μ_ℓ)` with the finite
group `Lˣ ⧸ (Lˣ)ˡ` of power classes (`TauCeti.ClassFieldTheory.finite_H1_kummerCoeff`), finite by
`TauCeti.finiteIndex_range_powMonoidHom`. The finite extension `L` is a nonarchimedean local field
for the spectral norm, `TauCeti.finiteExtension_isNonarchimedeanLocalField`.

In degree two the same reduction applies verbatim as soon as `H²(G_L, μ_ℓ)` is finite. That group
is the `ℓ`-torsion of the Brauer group of `L`, whose finiteness rests on the local invariant; this
file does not treat degree two.

## Main results

* `TauCeti.ClassFieldTheory.finite_H1_kummerCoeff`: `H¹(G_L, μ_ℓ)` is finite for a nonarchimedean
  local field `L` in which `ℓ` is invertible.
* `TauCeti.ClassFieldTheory.finite_continuousCohomology_of_le_one`: `Hⁱ(G_F, A)` is finite for
  `i ≤ 1` and every finite smooth discrete `A : GalRep n F`, `n` invertible in `F`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. II, §5.2, Proposition 14.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. VII, §1.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology TauCeti.ContinuousCohomology

universe u

/-- **`H¹(G_L, μ_ℓ)` is finite over a nonarchimedean local field** `L` in which `ℓ` is invertible:
by Kummer theory it is the group `Lˣ ⧸ (Lˣ)ˡ` of `ℓ`th power classes, which is finite. -/
theorem finite_H1_kummerCoeff (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] {ℓ : ℕ} (hℓ : (ℓ : L) ≠ 0) :
    Finite (H1 (AbsoluteGaloisGroup L) (KummerCoeff L ℓ)) := by
  have hP : powerSubgroup Lˣ ℓ = (powMonoidHom ℓ : Lˣ →* Lˣ).range := by
    ext; simp [mem_powerSubgroup_iff]
  have : (powerSubgroup Lˣ ℓ).FiniteIndex := hP ▸ finiteIndex_range_powMonoidHom hℓ
  have : Finite (powerClassQuotient Lˣ ℓ) := Subgroup.finite_quotient_of_finiteIndex
  exact Finite.of_equiv _ (kummerIso L ℓ (Ne.isUnit hℓ)).toEquiv

/-- **`H¹` of a cyclic trivial module over a local field containing the roots of unity.** Let `L`
be a nonarchimedean local field containing a primitive `ℓ`th root of unity, and `H` a topological
group isomorphic to `G_L`. Then `H¹(H, M)` is finite for every cyclic discrete `H`-module `M` of
order `ℓ` with trivial action: such a module is `μ_ℓ(Lˢ)` (`finite_H1_kummerCoeff`). -/
theorem finite_H1_of_isPrimitiveRoot (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] {ℓ : ℕ} [NeZero ℓ] {ζ : L} (hζ : IsPrimitiveRoot ζ ℓ)
    {H : Type u} [Group H] [TopologicalSpace H]
    (φ : AbsoluteGaloisGroup L ≃ₜ* H) (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction H M] [ContinuousSMul H M] [IsAddCyclic M]
    (hM : Nat.card M = ℓ)
    (htriv : ∀ (h : H) (m : M), h • m = m) :
    Finite (H1 H M) := by
  have := hζ.neZero'
  have := finite_H1_kummerCoeff L (NeZero.ne (ℓ : L))
  have hcard : Nat.card (KummerCoeff L ℓ) = Nat.card M :=
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (SeparableClosure L) ℓ).trans hM.symm
  exact Finite.of_equiv _ (explicitMap1Equiv H M (AbsoluteGaloisGroup L) (KummerCoeff L ℓ) φ
    (addEquivOfAddCyclicCardEq hcard.symm) continuous_of_discreteTopology
    continuous_of_discreteTopology fun g m ↦ by
      rw [htriv, smul_kummerCoeff_eq_self hζ]).symm.toEquiv

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

attribute [local instance] TopRep.distribMulAction

/-- **Finiteness of `H⁰` and `H¹` of a finite Galois module over a local field.** Let `F` be a
nonarchimedean local field and `n` a natural number invertible in `F`. For every finite smooth
discrete `G_F`-module `A` killed by `n`, the continuous cohomology `Hⁱ(G_F, A)` is finite for
`i ≤ 1`. -/
theorem finite_continuousCohomology_of_le_one (hn : (n : F) ≠ 0) (A : GalRep n F)
    (hA : IsSmoothDiscrete (ZMod n) A) [Finite A.V] {i : ℕ} (hi : i ≤ 1) :
    Finite (continuousCohomology i A) := by
  have := hA.discreteTopology
  have := hA.continuousSMul
  suffices Finite (continuousCohomology i (ofDiscreteModule ℤ (Field.absoluteGaloisGroup F) A.V))
    from Finite.of_equiv _ (ofDiscreteModuleRestrictScalarsIntEquiv A i).toEquiv
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
  · exact finite_continuousCohomology_zero _
  -- Structure of the proof: move `A` to `Γ = Gal(Fˢ/F)`, choose a finite Galois `L/F` trivializing
  -- `A` and containing `μ_n`, and apply the reduction through `Gal(Fˢ/L) ≅ G_L` to Kummer theory.
  -- transport the action to `Γ` along the restriction isomorphism `e`
  set e := absoluteGaloisGroupRestrictEquiv F
  let : DistribMulAction (AbsoluteGaloisGroup F) A.V :=
    DistribMulAction.compHom A.V (e.symm : AbsoluteGaloisGroup F →* Field.absoluteGaloisGroup F)
  -- the transported action unfolds to the action of `e.symm g`, by definition of `compHom`
  have hsmul (g : AbsoluteGaloisGroup F) (a : A.V) : g • a = e.symm g • a := (rfl)
  have : ContinuousSMul (AbsoluteGaloisGroup F) A.V :=
    ⟨(continuous_smul.comp ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd) :
      Continuous fun p : AbsoluteGaloisGroup F × A.V ↦ e.symm p.1 • p.2)⟩
  suffices Finite (continuousCohomology 1 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) A.V)) from
    Finite.of_equiv _ (((explicitH1AddEquivContinuousCohomology _ A.V).symm.trans
      (explicitMap1Equiv (AbsoluteGaloisGroup F) A.V (Field.absoluteGaloisGroup F) A.V e
        (AddEquiv.refl _) continuous_id continuous_id fun g a ↦ by
          rw [hsmul, ContinuousMulEquiv.symm_apply_apply]; rfl)).trans
      (explicitH1AddEquivContinuousCohomology _ A.V)).toEquiv
  -- a primitive `n`th root of unity `ζ` in `Fˢ`
  have : NeZero (n : F) := ⟨hn⟩
  have : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (SeparableClosure F) n
  -- an open normal subgroup `W` acting trivially on `A` and fixing `ζ`
  have hopen : IsOpen ({g : AbsoluteGaloisGroup F | ∀ a : A.V, g • a = a} ∩
      (MulAction.stabilizer (AbsoluteGaloisGroup F) ζ : Set (AbsoluteGaloisGroup F))) := by
    refine IsOpen.inter ?_ (stabilizer_isOpen_of_isIntegral ζ)
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun a ↦ (hA.stabilizer_isOpen a).preimage e.symm.continuous
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen
    ⟨fun a ↦ one_smul _ a, MulAction.one_smul ζ⟩
  -- its class field `L`, a nonarchimedean local field containing `ζ`
  set L := classField F W
  let := finiteExtensionValuativeRel F L
  let := finiteExtensionNormedFieldTopology F L
  have := finiteExtension_isNonarchimedeanLocalField F L
  have hζL : ζ ∈ L := mem_classField.2 fun g hg ↦ (hW hg).2
  have hζ' : IsPrimitiveRoot (⟨ζ, hζL⟩ : L) n :=
    IsPrimitiveRoot.of_map_of_injective (f := L.val) hζ L.val.injective
  -- the subgroup `V = Gal(Fˢ/L) ≅ G_L`, which is `W`
  set V := (galoisSubgroup F L L.val).toSubgroup
  have hVW : V = W.toSubgroup := (galoisSubgroup_toSubgroup F L L.val).trans <| by
    rw [IntermediateField.fieldRange_val]
    exact fixingSubgroup_classField W
  have : V.Normal := hVW ▸ W.isNormal'
  refine finite_continuousCohomology_of_isOpen_of_normal_of_prime V
    (galoisSubgroup F L L.val).isOpen 1 (N := n) ?_ A.V (fun a ↦ ?_)
    fun v hv a ↦ (hW (hVW ▸ hv : v ∈ W.toSubgroup)).1 a
  · intro j hj M _ _ _ _ _ _ hM hMn hMtriv
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj with rfl | rfl
    · exact finite_continuousCohomology_zero M
    -- `M` has prime order `ℓ ∣ n`, and `L` contains the primitive `ℓ`th root `ζ ^ (n / ℓ)`
    have : NeZero (Nat.card M) := ⟨hM.ne_zero⟩
    have : IsAddCyclic M := isAddCyclic_of_prime_card rfl (hp := ⟨hM⟩)
    have hζℓ : IsPrimitiveRoot ((⟨ζ, hζL⟩ : L) ^ (n / Nat.card M)) (Nat.card M) := by
      have h := hζ'.pow_of_dvd
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hMn) hM.pos).ne'
        (Nat.div_dvd_of_dvd hMn)
      rwa [Nat.div_div_self hMn (NeZero.ne n)] at h
    have := finite_H1_of_isPrimitiveRoot L hζℓ (galoisSubgroupEquiv F L L.val) M rfl hMtriv
    exact Finite.of_equiv _ (explicitH1AddEquivContinuousCohomology V M).toEquiv
  · -- `A` is killed by `n`, being a `ZMod n`-module
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]

end TauCeti.ClassFieldTheory

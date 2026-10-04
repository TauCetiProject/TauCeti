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
public import TauCeti.NumberTheory.LocalField.Kummer
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
coinduction from the image in `G_F` of the subgroup `Gal(Fˢ/L) ≅ G_L` and dévissage, leaves the
trivial `G_L`-modules of prime order `ℓ ∣ n`. Such a module is `μ_ℓ(Lˢ)`, because `L` contains the
`ℓ`th roots of unity, and the Kummer isomorphism `TauCeti.kummerIso` identifies `H¹(G_L, μ_ℓ)` with
the group `Lˣ ⧸ (Lˣ)ˡ` of power classes, finite since `L` is a local field
(`TauCeti.finite_H1_of_isPrimitiveRoot_of_natCard_dvd`). The finite extension `L` is a
nonarchimedean local field for the spectral norm,
`TauCeti.finiteExtension_isNonarchimedeanLocalField`.

In degree two the same reduction applies verbatim as soon as `H²(G_L, μ_ℓ)` is finite. That group
is the `ℓ`-torsion of the Brauer group of `L`, whose finiteness rests on the local invariant; this
file does not treat degree two.

## Main results

* `TauCeti.ClassFieldTheory.exists_classField_trivializing`: a finite smooth Galois module becomes
  trivial over a finite Galois extension containing the roots of unity of its exponent.
* `TauCeti.ClassFieldTheory.finite_continuousCohomology_of_prime_ge_two`: reduction to trivial
  prime-order coefficients in degrees at least two over local fields containing roots of unity.
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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

attribute [local instance] TopRep.distribMulAction

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A finite smooth Galois module becomes trivial over a finite Galois extension containing
all the roots of unity of its exponent. The extension is presented by its open normal subgroup. -/
theorem exists_classField_trivializing (hn : (n : F) ≠ 0) (A : GalRep n F)
    (hA : IsSmoothDiscrete (ZMod n) A) [Finite A.V] :
    ∃ W : OpenNormalSubgroup (AbsoluteGaloisGroup F),
      (∃ ζ : classField F W, IsPrimitiveRoot ζ n) ∧
      ∀ g ∈ W, ∀ a : A.V, (absoluteGaloisGroupRestrictEquiv F).symm g • a = a := by
  have := hA.discreteTopology
  have := hA.continuousSMul
  have : NeZero (n : F) := ⟨hn⟩
  have : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  set e := absoluteGaloisGroupRestrictEquiv F
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (SeparableClosure F) n
  have hopen : IsOpen ({g : AbsoluteGaloisGroup F | ∀ a : A.V, e.symm g • a = a} ∩
      (MulAction.stabilizer (AbsoluteGaloisGroup F) ζ : Set (AbsoluteGaloisGroup F))) := by
    refine IsOpen.inter ?_ (stabilizer_isOpen_of_isIntegral ζ)
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun a ↦ (hA.stabilizer_isOpen a).preimage e.symm.continuous
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen
    ⟨fun a ↦ by rw [map_one, one_smul], MulAction.one_smul ζ⟩
  have hζL : ζ ∈ classField F W := mem_classField.2 fun g hg ↦ (hW hg).2
  exact ⟨W, ⟨⟨⟨ζ, hζL⟩, IsPrimitiveRoot.of_map_of_injective
    (f := (classField F W).val) hζ (classField F W).val.injective⟩,
    fun g hg ↦ (hW hg).1⟩⟩

/-- Finiteness of local Galois cohomology reduces to trivial modules of prime order over
local fields containing the roots of unity of the exponent. Only degrees `2 ≤ j ≤ i` need
arithmetic input; degree one follows from Kummer theory. The test group can be any compact
topological copy of the absolute Galois group of such a field. -/
theorem finite_continuousCohomology_of_prime_ge_two (hn : (n : F) ≠ 0) (A : GalRep n F)
    (hA : IsSmoothDiscrete (ZMod n) A) [Finite A.V] (i : ℕ)
    (h : ∀ (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
      [IsNonarchimedeanLocalField L] {ζ : L}, IsPrimitiveRoot ζ n →
      ∀ (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H],
      (AbsoluteGaloisGroup L ≃ₜ* H) → ∀ j, 1 < j → j ≤ i →
      ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction H M] [ContinuousSMul H M] [Finite M],
      (Nat.card M).Prime → Nat.card M ∣ n → (∀ (g : H) (m : M), g • m = m) →
      Finite (continuousCohomology j (ofDiscreteModule ℤ H M))) :
    Finite (continuousCohomology i A) := by
  have := hA.discreteTopology
  have := hA.continuousSMul
  suffices Finite (continuousCohomology i (ofDiscreteModule ℤ (Field.absoluteGaloisGroup F) A.V))
    from Finite.of_equiv _ (ofDiscreteModuleRestrictScalarsIntEquiv A i).toEquiv
  -- Choose a finite Galois extension trivializing the action and containing the roots of unity.
  have : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  set e := absoluteGaloisGroupRestrictEquiv F
  obtain ⟨W, ⟨ζ, hζ'⟩, hW⟩ := exists_classField_trivializing hn A hA
  set L := classField F W
  let := finiteExtensionValuativeRel F L
  let := finiteExtensionNormedFieldTopology F L
  have := finiteExtension_isNonarchimedeanLocalField F L
  -- the subgroup `U = Gal(Fˢ/L) ≅ G_L`, which is `W`, and its image `V ≅ U` in `G_F`
  set U := (galoisSubgroup F L L.val).toSubgroup
  have hUW : U = W.toSubgroup := (galoisSubgroup_toSubgroup F L L.val).trans <| by
    rw [IntermediateField.fieldRange_val]
    exact fixingSubgroup_classField W
  set V := U.map (e.symm : AbsoluteGaloisGroup F →* Field.absoluteGaloisGroup F)
  have : V.Normal := (hUW ▸ W.isNormal' : U.Normal).map _ e.symm.surjective
  let ψ : U ≃ₜ* V :=
    { e.symm.toMulEquiv.subgroupMap U with
      continuous_toFun := continuous_induced_rng.2 (e.symm.continuous.comp continuous_subtype_val)
      continuous_invFun := continuous_induced_rng.2 (e.continuous.comp continuous_subtype_val) }
  have hV : IsOpen (V : Set (Field.absoluteGaloisGroup F)) :=
    e.symm.isOpenMap _ (galoisSubgroup F L L.val).isOpen
  have : CompactSpace V := isCompact_iff_compactSpace.mp (V.isClosed_of_isOpen hV).isCompact
  refine finite_continuousCohomology_of_isOpen_of_normal_of_prime (V := V)
    hV i (N := n) ?_ A.V (fun a ↦ ?_)
    fun v hv a ↦ ?_
  · intro j hj₀ hj M _ _ _ _ _ _ hM hMn hMtriv
    by_cases hj₁ : j = 1
    · subst j
      have := isAddCyclic_of_prime_card rfl (hp := ⟨hM⟩)
      have := finite_H1_of_isPrimitiveRoot_of_natCard_dvd L hζ'
        ((galoisSubgroupEquiv F L L.val).trans ψ) M hMn hMtriv
      exact Finite.of_equiv _ (explicitH1AddEquivContinuousCohomology V M).toEquiv
    · exact h L hζ' V ((galoisSubgroupEquiv F L L.val).trans ψ) j
        (by omega) hj M hM hMn hMtriv
  · -- `A` is killed by `n`, being a `ZMod n`-module
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  · -- `V` acts trivially on `A`, being the image of `U = W`
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hv
    exact hW u (hUW ▸ hu : u ∈ W.toSubgroup) a

/-- **Finiteness of `H⁰` and `H¹` of a finite Galois module over a local field.** Let `F` be a
nonarchimedean local field and `n` a natural number invertible in `F`. For every finite smooth
discrete `G_F`-module `A` killed by `n`, the continuous cohomology `Hⁱ(G_F, A)` is finite for
`i ≤ 1`. -/
theorem finite_continuousCohomology_of_le_one (hn : (n : F) ≠ 0) (A : GalRep n F)
    (hA : IsSmoothDiscrete (ZMod n) A) [Finite A.V] {i : ℕ} (hi : i ≤ 1) :
    Finite (continuousCohomology i A) := by
  exact finite_continuousCohomology_of_prime_ge_two hn A hA i
    fun _ _ _ _ _ _ _ _ _ _ _ _ j hj₀ hj ↦ by omega

end TauCeti.ClassFieldTheory

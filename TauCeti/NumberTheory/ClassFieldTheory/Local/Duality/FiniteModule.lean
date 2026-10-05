/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.TrivialAction
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.KummerCorestriction
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.TrivialZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.DimensionShifting
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.OpenSubgroup
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Local Tate duality for finite Galois modules

Let `K` be a nonarchimedean local field, `n` a natural number invertible in `K`, and `μₙ` the
`n`th roots of unity of a separable closure `Kˢ`, the `G_K`-module `TauCeti.KummerCoeff K n`. For a
finite discrete `G_K`-module `A` killed by `n`, write `A' = Hom(A, μₙ)` for its dual (the internal
hom `TauCeti.InternalHom`) and

```text
αᵢ : Hⁱ(G_K, A) → Hom(H²⁻ⁱ(G_K, A'), H²(G_K, μₙ)),   i = 0, 1, 2,
```

for Tate's duality maps (`TauCeti.ContCohomology.dualityMap0`, `dualityMap1`, `dualityMap2`). This
file proves **Tate's local duality theorem** in this form: the three maps `αᵢ` are bijective for
every such `A` (`TauCeti.ClassFieldTheory.dualityMap0_kummerCoeff_bijective` and its companions in
degrees `1` and `2`). No filtration of `A` by modules with trivial action is used, and none need
exist: over `ℚ₂`, the unramified action of order two on `ℤ/3` has none.

The proof goes up from the trivial-action case in three steps.

* **Open subgroups.** An open subgroup `V` of `G_K` acting trivially on `μₙ` is the absolute Galois
  group of its fixed field `E`, a finite extension of `K` containing a primitive `n`th root of
  unity `ζ`. Through `ζ`, the `V`-modules `μₙ` and `ℤ/n` with trivial action are isomorphic, and
  Tate's duality for finite modules with trivial action over `E`
  (`TauCeti.ClassFieldTheory.dualityMap0_bijective_of_isPrimitiveRoot` and its companions) gives the
  bijectivity of the three duality maps of `V` on every finite `V`-module with trivial action
  killed by `n` (`TauCeti.ClassFieldTheory.dualityMap_bijective_of_smul_kummerCoeff_eq_self`).
* **Shapiro's lemma.** Corestriction `H²(V, μₙ) → H²(G_K, μₙ)` is bijective
  (`TauCeti.ClassFieldTheory.explicitCor2_kummerCoeff_bijective`), so Shapiro's lemma carries this
  duality to the `G_K`-module `Coind_V^{G_K} A`
  (`TauCeti.ContCohomology.dualityMap0_bijective_discreteCoind_of_bijective` and its companions),
  which is `TauCeti.ClassFieldTheory.dualityMap_bijective_discreteCoind_kummerCoeff`.
* **Dimension shifting.** For a general finite `A` killed by `n`, choose an open normal subgroup
  `V` acting trivially on `A` and on `μₙ`. Along `0 → A → Coind_V^{G_K} A → C → 0`, the four lemma
  and a count of orders pass from the coinduced modules to `A`
  (`TauCeti.ContCohomology.dualityMap0_bijective_of_bijective_discreteCoind` and its companions),
  using `H²(G_K, μₙ) ≃ ℤ/n` (`TauCeti.ClassFieldTheory.h2MuEquivZMod`) and the finiteness of
  `H¹(G_K, A')`, which reduces in the same way to the finiteness of `H¹(V, ℤ/ℓ) = Eˣ/(Eˣ)ˡ`.

The statements are made on the explicit low-degree cochain model with the single ambient
coefficient module `μₙ = KummerCoeff K n`, which is the model of the generic duality, Shapiro and
corestriction API they are assembled from.

## Main results

* `TauCeti.ClassFieldTheory.dualityMap_bijective_of_smul_kummerCoeff_eq_self`: Tate's duality for
  an open subgroup of `G_K` acting trivially on `μₙ`, on its finite modules with trivial action.
* `TauCeti.ClassFieldTheory.dualityMap_bijective_discreteCoind_kummerCoeff`: Tate's duality for the
  modules coinduced from such a subgroup.
* `TauCeti.ClassFieldTheory.dualityMap0_kummerCoeff_bijective`,
  `dualityMap1_kummerCoeff_bijective` and `dualityMap2_kummerCoeff_bijective`: **local Tate
  duality** for every finite discrete `G_K`-module killed by `n`.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter II, §5.2, Theorem 2 and its proof.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.2.6).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Theorem 2.1 and its proof.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {n : ℕ}

/-- The roots of unity `μₙ` of `Kˢ` form a cyclic group of order `n`, for `n` invertible in `K`. -/
private noncomputable def kummerCoeffAddEquivZMod (hn : IsUnit (n : K)) :
    KummerCoeff K n ≃+ ZMod n :=
  have : NeZero (n : K) := ⟨hn.ne_zero⟩
  have : NeZero n := NeZero.of_neZero_natCast K
  addEquivOfAddCyclicCardEq <| by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (SeparableClosure K) n
    rw [Nat.card_zmod]
    exact (Nat.card_congr Additive.toMul).trans hζ.card_rootsOfUnity

/-- An open subgroup `V` of `G_K` acting trivially on `μₙ` is the absolute Galois group of a local
field containing a primitive `n`th root of unity: a statement about such a field and a topological
copy of its absolute Galois group holds for `V`. The field is the fixed field of `V`. -/
private theorem of_isOpen_of_smul_kummerCoeff_eq_self (hn : IsUnit (n : K))
    (V : Subgroup (AbsoluteGaloisGroup K))
    (hV : IsOpen (V : Set (AbsoluteGaloisGroup K)))
    (hVN : ∀ v ∈ V, ∀ y : KummerCoeff K n, v • y = y) {P : Prop}
    (h : ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
      [IsNonarchimedeanLocalField E] {ζ : E}, IsPrimitiveRoot ζ n → (AbsoluteGaloisGroup E ≃ₜ* V) →
      P) : P := by
  have : NeZero (n : K) := ⟨hn.ne_zero⟩
  have : NeZero n := NeZero.of_neZero_natCast K
  -- `V` is the subgroup fixing its fixed field `E`, which is finite over `K`.
  obtain ⟨E, _, rfl⟩ : ∃ E : IntermediateField K (SeparableClosure K),
      FiniteDimensional K E ∧ E.val.fieldRange.fixingSubgroup = V := by
    obtain ⟨E, hE⟩ : ∃ E : IntermediateField K (SeparableClosure K), E.fixingSubgroup = V :=
      ⟨_, InfiniteGalois.fixingSubgroup_fixedField ⟨V, Subgroup.isClosed_of_isOpen V hV⟩⟩
    refine ⟨E, ?_, by rw [IntermediateField.fieldRange_val, hE]⟩
    rw [← InfiniteGalois.isOpen_iff_finite, hE]
    exact hV
  let _ := finiteExtensionValuativeRel K E
  let _ := finiteExtensionNormedFieldTopology K E
  have := finiteExtension_isNonarchimedeanLocalField K E
  -- A primitive `n`th root of unity of `Kˢ` is fixed by `V`, so it lies in `E`.
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (SeparableClosure K) n
  have hζE : ζ ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h := congrArg (fun y : KummerCoeff K n ↦ ((y.toMul : (SeparableClosure K)ˣ) :
      SeparableClosure K)) (hVN σ (by rwa [IntermediateField.fieldRange_val])
        (Additive.ofMul hζ.toRootsOfUnity))
    simpa using h
  exact h E (ζ := ⟨ζ, hζE⟩) (IsPrimitiveRoot.of_map_of_injective (f := E.val) hζ E.val.injective)
    (absoluteGaloisGroupEquivFixingSubgroup K E E.val)

section OpenSubgroup

variable (hn : IsUnit (n : K)) (V : Subgroup (AbsoluteGaloisGroup K))
  (hV : IsOpen (V : Set (AbsoluteGaloisGroup K)))
  (hVN : ∀ v ∈ V, ∀ y : KummerCoeff K n, v • y = y)
  (A : Type) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction V A]
  [ContinuousSMul V A] [Finite A] (hA : ∀ a : A, n • a = 0) (hAV : ∀ (v : V) (a : A), v • a = a)

include hn hV hVN hA hAV

/-- **Tate's duality on an open subgroup acting trivially on `μₙ`.** Let `V` be an open subgroup of
`G_K` acting trivially on `μₙ`, for `n` invertible in the local field `K`. For every finite discrete
`V`-module `A` killed by `n` on which `V` acts trivially, the three duality maps
`Hⁱ(V, A) → Hom(H²⁻ⁱ(V, Hom(A, μₙ)), H²(V, μₙ))` are bijective. -/
theorem dualityMap_bijective_of_smul_kummerCoeff_eq_self :
    Function.Bijective (dualityMap0 V A (KummerCoeff K n)) ∧
      Function.Bijective (dualityMap1 V A (KummerCoeff K n)) ∧
        Function.Bijective (dualityMap2 V A (KummerCoeff K n)) := by
  have : NeZero n := NeZero.of_neZero_natCast K (h := ⟨hn.ne_zero⟩)
  refine of_isOpen_of_smul_kummerCoeff_eq_self hn V hV hVN fun E _ _ _ _ ζ hζ φ ↦ ?_
  -- Through `ζ`, `μₙ` is the trivial `V`-module `ℤ/n`.
  let _ := trivialZModAction n V
  have : ContinuousSMul V (ZMod n) := ⟨continuous_snd⟩
  have htriv : ∀ (v : V) (m : ZMod n), v • m = m := fun _ _ ↦ rfl
  let f : KummerCoeff K n →+[V] ZMod n :=
    { (kummerCoeffAddEquivZMod hn).toAddMonoidHom with
      map_smul' := fun v y ↦ by
        rw [Subgroup.smul_def, hVN v v.2 y, MonoidHom.id_apply, htriv] }
  have hf : Function.Bijective f := (kummerCoeffAddEquivZMod hn).bijective
  exact ⟨(dualityMap0_bijective_iff_of_bijective hf).2
      (dualityMap0_bijective_of_isPrimitiveRoot hζ φ htriv A hA hAV),
    (dualityMap1_bijective_iff_of_bijective hf).2
      (dualityMap1_bijective_of_isPrimitiveRoot hζ φ htriv A hA hAV),
    (dualityMap2_bijective_iff_of_bijective hf).2
      (dualityMap2_bijective_of_isPrimitiveRoot hζ φ htriv A hA hAV)⟩

/-- **Tate's duality on a module coinduced from an open subgroup acting trivially on `μₙ`.** Let
`V` be an open subgroup of `G_K` acting trivially on `μₙ`, for `n` invertible in the local field
`K`, and `A` a finite discrete `V`-module killed by `n` on which `V` acts trivially. Then the three
duality maps of `G_K` are bijective on `Coind_V^{G_K} A`: by Shapiro's lemma they are those of `V`
on `A`, followed by corestriction on `H²(-, μₙ)`, which is bijective. -/
theorem dualityMap_bijective_discreteCoind_kummerCoeff [V.FiniteIndex] :
    Function.Bijective
        (dualityMap0 (AbsoluteGaloisGroup K) (DiscreteCoind (AbsoluteGaloisGroup K) V A)
          (KummerCoeff K n)) ∧
      Function.Bijective
        (dualityMap1 (AbsoluteGaloisGroup K) (DiscreteCoind (AbsoluteGaloisGroup K) V A)
          (KummerCoeff K n)) ∧
        Function.Bijective
          (dualityMap2 (AbsoluteGaloisGroup K) (DiscreteCoind (AbsoluteGaloisGroup K) V A)
            (KummerCoeff K n)) := by
  have hcor := explicitCor2_kummerCoeff_bijective K hn V hV
  obtain ⟨h₀, h₁, h₂⟩ := dualityMap_bijective_of_smul_kummerCoeff_eq_self hn V hV hVN A hA hAV
  exact ⟨dualityMap0_bijective_discreteCoind_of_bijective _ V hV A _ hcor h₀,
    dualityMap1_bijective_discreteCoind_of_bijective _ V hV A _ hcor h₁,
    dualityMap2_bijective_discreteCoind_of_bijective _ V hV A _ hcor h₂⟩

end OpenSubgroup

section FiniteModule

variable (hn : IsUnit (n : K)) (V : Subgroup (AbsoluteGaloisGroup K))
  (hV : IsOpen (V : Set (AbsoluteGaloisGroup K)))
  (hVN : ∀ v ∈ V, ∀ y : KummerCoeff K n, v • y = y)
  (A : Type) [AddCommGroup A] [TopologicalSpace A]
  [DiscreteTopology A] [DistribMulAction (AbsoluteGaloisGroup K) A]
  [ContinuousSMul (AbsoluteGaloisGroup K) A] [Finite A] (hA : ∀ a : A, n • a = 0)
  (hAV : ∀ v ∈ V, ∀ a : A, v • a = a)

include hn hV hVN hA hAV

/-- `H¹(G_K, Hom(A, μₙ))` is finite: `V` acts trivially on `Hom(A, μₙ)`, which reduces the claim
to the finiteness of `H¹(V, ℤ/ℓ)` for the primes `ℓ ∣ n`, a group of power classes of the fixed
field of `V`. -/
private theorem finite_H1_internalHom_kummerCoeff [V.Normal] :
    Finite (H1 (AbsoluteGaloisGroup K)
      (InternalHom (AbsoluteGaloisGroup K) A (KummerCoeff K n))) := by
  have : NeZero n := NeZero.of_neZero_natCast K (h := ⟨hn.ne_zero⟩)
  refine of_isOpen_of_smul_kummerCoeff_eq_self hn V hV hVN fun E _ _ _ _ ζ hζ φ ↦ ?_
  have := TauCeti.ContinuousCohomology.finite_continuousCohomology_of_isOpen_of_normal_of_prime
    hV 1 (N := n) (fun j hj₀ hj M _ _ _ _ _ _ hM hMn hMtriv ↦ by
      obtain rfl : j = 1 := by omega
      have := isAddCyclic_of_prime_card rfl (hp := ⟨hM⟩)
      have := finite_H1_of_isPrimitiveRoot_of_natCard_dvd E hζ φ M hMn hMtriv
      exact Finite.of_equiv _ (explicitH1AddEquivContinuousCohomology _ M).toEquiv)
    (InternalHom (AbsoluteGaloisGroup K) A (KummerCoeff K n))
    (InternalHom.nsmul_eq_zero_of_domain hA)
    fun v hv φ ↦ InternalHom.smul_eq_self_iff.2 fun a ↦ by rw [hAV v hv, hVN v hv]
  exact Finite.of_equiv _ (explicitH1AddEquivContinuousCohomology _ _).symm.toEquiv

/-- The three duality maps of `G_K` with coefficients in `μₙ` are bijective on `A` once an open
normal subgroup `V` acts trivially on `A` and on `μₙ`: dimension shifting along
`0 → A → Coind_V^{G_K} A → C → 0`, from Tate's duality on the coinduced modules. -/
private theorem dualityMap_kummerCoeff_bijective_of_smul_eq_self [V.Normal] [V.FiniteIndex] :
    Function.Bijective (dualityMap0 (AbsoluteGaloisGroup K) A (KummerCoeff K n)) ∧
      Function.Bijective (dualityMap1 (AbsoluteGaloisGroup K) A (KummerCoeff K n)) ∧
        Function.Bijective (dualityMap2 (AbsoluteGaloisGroup K) A (KummerCoeff K n)) :=
  have : NeZero n := NeZero.of_neZero_natCast K (h := ⟨hn.ne_zero⟩)
  have e₂ : H2 (AbsoluteGaloisGroup K) (KummerCoeff K n) ≃+ ZMod n :=
    (muNRepH2Equiv n K).trans (h2MuEquivZMod K hn)
  have := finite_H1_internalHom_kummerCoeff hn V hV hVN A hA hAV
  have hcoind := fun (B : Type) [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
      [DistribMulAction (AbsoluteGaloisGroup K) B] [ContinuousSMul (AbsoluteGaloisGroup K) B]
      [Finite B] (hB : ∀ b : B, n • b = 0) (hBV : ∀ v ∈ V, ∀ b : B, v • b = b) ↦
    (dualityMap_bijective_discreteCoind_kummerCoeff hn V hV hVN B hB
      fun v b ↦ hBV v v.2 b).imp_right (And.imp_right And.left)
  ⟨dualityMap0_bijective_of_bijective_discreteCoind (kummerCoeffAddEquivZMod hn) e₂ hVN hcoind A
      hA hAV,
    dualityMap1_bijective_of_injective_discreteCoind (kummerCoeffAddEquivZMod hn) e₂ hVN
      (fun B _ _ _ _ _ _ hB hBV ↦ ⟨(hcoind B hB hBV).1, (hcoind B hB hBV).2.1.1⟩) A hA hAV,
    dualityMap2_bijective_of_bijective_discreteCoind (kummerCoeffAddEquivZMod hn) e₂ hVN hcoind A
      hA hAV⟩

omit hV hVN hAV

/-- The three duality maps of `G_K` with coefficients in `μₙ` are bijective on `A`, through an
open normal subgroup acting trivially on `A` and on `μₙ`. -/
private theorem dualityMap_kummerCoeff_bijective :
    Function.Bijective (dualityMap0 (AbsoluteGaloisGroup K) A (KummerCoeff K n)) ∧
      Function.Bijective (dualityMap1 (AbsoluteGaloisGroup K) A (KummerCoeff K n)) ∧
        Function.Bijective (dualityMap2 (AbsoluteGaloisGroup K) A (KummerCoeff K n)) :=
  have : NeZero n := NeZero.of_neZero_natCast K (h := ⟨hn.ne_zero⟩)
  ((Set.finite_univ (α := KummerCoeff K n)).exists_openNormalSubgroup_smul_eq_self
    (G := AbsoluteGaloisGroup K)).elim fun W₁ h₁ ↦
  ((Set.finite_univ (α := A)).exists_openNormalSubgroup_smul_eq_self
    (G := AbsoluteGaloisGroup K)).elim fun W₂ h₂ ↦
  dualityMap_kummerCoeff_bijective_of_smul_eq_self hn (W₁ ⊓ W₂).toSubgroup (W₁ ⊓ W₂).isOpen
    (fun v hv y ↦ h₁ v hv.1 y trivial) A hA fun v hv a ↦ h₂ v hv.2 a trivial

/-- **Local Tate duality in degree zero.** Let `K` be a nonarchimedean local field and `n` a natural
number invertible in `K`. For every finite discrete `G_K`-module `A` killed by `n`, Tate's duality
map `H⁰(G_K, A) → Hom(H²(G_K, Hom(A, μₙ)), H²(G_K, μₙ))` is bijective. -/
theorem dualityMap0_kummerCoeff_bijective :
    Function.Bijective (dualityMap0 (AbsoluteGaloisGroup K) A (KummerCoeff K n)) :=
  (dualityMap_kummerCoeff_bijective hn A hA).1

/-- **Local Tate duality in degree one.** Let `K` be a nonarchimedean local field and `n` a natural
number invertible in `K`. For every finite discrete `G_K`-module `A` killed by `n`, Tate's duality
map `H¹(G_K, A) → Hom(H¹(G_K, Hom(A, μₙ)), H²(G_K, μₙ))` is bijective. -/
theorem dualityMap1_kummerCoeff_bijective :
    Function.Bijective (dualityMap1 (AbsoluteGaloisGroup K) A (KummerCoeff K n)) :=
  (dualityMap_kummerCoeff_bijective hn A hA).2.1

/-- **Local Tate duality in degree two.** Let `K` be a nonarchimedean local field and `n` a natural
number invertible in `K`. For every finite discrete `G_K`-module `A` killed by `n`, Tate's duality
map `H²(G_K, A) → Hom(H⁰(G_K, Hom(A, μₙ)), H²(G_K, μₙ))` is bijective. -/
theorem dualityMap2_kummerCoeff_bijective :
    Function.Bijective (dualityMap2 (AbsoluteGaloisGroup K) A (KummerCoeff K n)) :=
  (dualityMap_kummerCoeff_bijective hn A hA).2.2

end FiniteModule

end TauCeti.ClassFieldTheory

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.DecompositionRestrict
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.NumberTheory.NumberField.Ideal.ArtinMap
public import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.GroupTheory.Abelianization.Basic
import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
import TauCeti.NumberTheory.NumberField.LocalGlobal.Frobenius
import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex
import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# The local Artin symbols of a number field in a finite Galois extension

Let `L/K` be a finite normal extension of number fields and `v` a finite place of `K` with
completion `K_v`. The absolute local Artin map `artinMap K_v : K_vˣ → G_{K_v}^ab`, read in
`Gal(L/K)^ab` by restricting along a place of `L` above `v`
(`TauCeti.decompositionRestrict`), is the **local Artin symbol at `v`**

```text
localArtinAt K L v : K_vˣ →* Gal(L/K)^ab.
```

In global class field theory it is the local factor of the global Artin map: the global Artin
symbol of an idele is the product of the local Artin symbols of its components. It is compatible
with restriction to a normal subextension (`localArtinAt_comp`).

For `L/K` Galois and a finite place `w` of `L` above `v`, the decomposition group of `w` is the
Galois group of `L_w/K_v` (`IsDedekindDomain.HeightOneSpectrum.decompositionEquiv`), and the local
Artin symbol at `v` is finite local reciprocity for `L_w/K_v`, read in `Gal(L/K)^ab` through that
identification (`localArtinAt_eq_map_normResidue`). Consequently:

* the local norms `N_{L_w/K_v}(L_wˣ)` lie in its kernel (`normGroup_le_ker_localArtinAt`), with
  equality when `L/K` is abelian (`localArtinAt_eq_one_iff_mem_normGroup`), and its image is the
  image of the decomposition group of `w` (`range_localArtinAt`);
* at a place unramified in `L`, it is an arithmetic Frobenius at `w` raised to the normalized
  valuation (`localArtinAt_eq_of_isArithFrobAt`): a uniformizer goes to Frobenius
  (`localArtinAt_uniformizer_eq_of_isArithFrobAt`) and a unit to `1`
  (`localArtinAt_eq_one_of_normalizedValuation_eq_one`). For abelian `L/K` this Frobenius is the
  Artin automorphism `TauCeti.NumberFieldArithmetic.artinElement` of the ideal-theoretic Artin map
  (`localArtinAt_eq_artinElement_zpow`).

The last statement is the arithmetic content of the comparison between the global Artin map and
the ideal-theoretic one at the unramified primes.

## Main definitions

* `TauCeti.ClassFieldTheory.localArtinAt K L v`: the local Artin symbol at `v`, with values in
  `Gal(L/K)^ab`.

## Main results

* `TauCeti.ClassFieldTheory.localArtinAt_eq_of_mk_eq_artinMap`: the local Artin symbol of `x` is
  the class of the automorphism of `L` induced, along any embedding of `L` into `K_vᵃˡᵍ`, by a
  representative of the absolute Artin symbol of `x`.
* `TauCeti.ClassFieldTheory.localArtinAt_comp`: compatibility with restriction to a normal
  subextension.
* `TauCeti.ClassFieldTheory.localArtinAt_norm`: compatibility with the local norm from a
  finite place of an intermediate field.
* `TauCeti.ClassFieldTheory.localArtinAt_eq_map_normResidue`: the local Artin symbol at `v` is
  finite local reciprocity for `L_w/K_v`, read through the decomposition group of `w`.
* `TauCeti.ClassFieldTheory.normGroup_le_ker_localArtinAt`: local norms have trivial local Artin
  symbol; `TauCeti.ClassFieldTheory.localArtinAt_eq_one_iff_mem_normGroup`: for `L/K` abelian,
  exactly the local norms do.
* `TauCeti.ClassFieldTheory.range_localArtinAt`: the image of the local Artin symbol is the image
  of the decomposition group.
* `TauCeti.ClassFieldTheory.localArtinAt_eq_of_isArithFrobAt`: at an unramified place, the local
  Artin symbol of `x` is an arithmetic Frobenius raised to the normalized valuation of `x`.
* `TauCeti.ClassFieldTheory.localArtinAt_eq_artinElement_zpow`: for `L/K` abelian, that
  Frobenius is the Artin automorphism of the ideal-theoretic Artin map.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9 (decomposition groups and completions)
  and Chapter VI, §5 (the global reciprocity law and its local factors).
-/
public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField
open scoped AdicCompletionExtension Pointwise

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [Algebra K L]

/-! ### The local Artin symbol -/

section Normal

variable [FiniteDimensional K L] [Normal K L]

/-- **The local Artin symbol at a finite place** `v` of a number field `K`, with values in the
abelianized Galois group of a finite normal extension `L/K`: the absolute local Artin map of the
completion `K_v`, read in `Gal(L/K)^ab` by restriction along a place of `L` above `v`
(`TauCeti.decompositionRestrict`). It does not depend on the choice of that place. -/
def localArtinAt (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* Abelianization Gal(L/K) :=
  (decompositionRestrict K (v.adicCompletion K) L).comp (artinMap (v.adicCompletion K))

variable {K L}

/-- The local Artin symbol at `v` is the absolute local Artin map of `K_v` followed by
restriction to `L`. -/
theorem localArtinAt_apply (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    localArtinAt K L v x =
      decompositionRestrict K (v.adicCompletion K) L (artinMap (v.adicCompletion K) x) :=
  (rfl)

/-- **The local Artin symbol through a representative.** If `τ ∈ G_{K_v}` represents the absolute
local Artin symbol of `x`, then for every `K`-embedding `j : L → K_vᵃˡᵍ` the local Artin symbol of
`x` at `v` is the class of the automorphism `σ` of `L` with `j ∘ σ = τ ∘ j`. -/
theorem localArtinAt_eq_of_mk_eq_artinMap (v : HeightOneSpectrum (𝓞 K))
    {x : (v.adicCompletion K)ˣ} (τ : Field.absoluteGaloisGroup (v.adicCompletion K))
    (hτ : (τ : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
      artinMap (v.adicCompletion K) x)
    (j : L →ₐ[K] AlgebraicClosure (v.adicCompletion K)) (σ : Gal(L/K))
    (hσ : ∀ y : L, j (σ y) = τ.toRingEquiv (j y)) :
    localArtinAt K L v x = Abelianization.of σ := by
  rw [localArtinAt_apply, ← hτ, decompositionRestrict_mk j τ σ hσ]

/-- **Compatibility with restriction to a normal subextension.** For a `K`-embedding
`f : M → L` of a finite normal extension `M/K`, the local Artin symbol at `v` in `Gal(L/K)^ab`,
restricted to `M` along `f`, is the local Artin symbol at `v` in `Gal(M/K)^ab`. -/
theorem localArtinAt_comp (v : HeightOneSpectrum (𝓞 K)) {M : Type} [Field M] [Algebra K M]
    [FiniteDimensional K M] [Normal K M] (f : M →ₐ[K] L) :
    (Abelianization.map f.restrictNormalHom).comp (localArtinAt K L v) = localArtinAt K M v := by
  rw [localArtinAt, localArtinAt, ← MonoidHom.comp_assoc, decompositionRestrict_comp]

/-- **Norm functoriality in the ground field.** Let `K ⊆ E ⊆ L` with `L/K` finite normal, and let
`w` be a finite place of `E` above the finite place `v` of `K`. The local Artin symbol at `v` of
the local norm `N_{E_w/K_v}(y)` is the local Artin symbol at `w` of `y`, read in `Gal(L/K)^ab`
through the inclusion `Gal(L/E) ≤ Gal(L/K)`:

```text
Art_v (N_{E_w/K_v} y) = Art_w y.
```

It is the norm functoriality `artinMap_norm` of the absolute local Artin maps, read through the
decomposition groups. The instances on `L/E` follow from those on `L/K`. -/
theorem localArtinAt_norm {E : Type} [Field E] [NumberField E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L] [FiniteDimensional E L] [Normal E L] (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] (y : (w.adicCompletion E)ˣ) :
    localArtinAt K L v (Algebra.normUnits (v.adicCompletion K) y) =
      Abelianization.map (AlgEquiv.restrictScalarsHom K) (localArtinAt E L w y) := by
  -- Represent `Art_w y` by `τ ∈ G_{E_w}`; then `Art_v (N y)` is represented by its image in
  -- `G_{K_v}` along an embedding `iota` of `E_w` in `K_vˢ`.
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (artinMap (w.adicCompletion E) y)
  let iota : w.adicCompletion E →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K) :=
    IsSepClosed.lift
  rw [localArtinAt_apply, localArtinAt_apply, ← artinMap_norm _ iota y τ hτ, ← hτ]
  -- Restrict `τ` to `σ ∈ Gal(L/E)` along an embedding `j` of `L` in `E_wˢ`.
  let j : L →ₐ[E] SeparableClosure (w.adicCompletion E) := IsSepClosed.lift
  let τ' := absoluteGaloisGroupRestrictEquiv (w.adicCompletion E) τ
  let σ : Gal(L/E) := j.restrictNormalHom (AlgEquiv.restrictScalarsHom E τ')
  have hσ (x : L) : j (σ x) = τ' (j x) := j.restrictNormalHom_commutes _ x
  -- Transporting `j` along the identification `φ` of `E_wˢ` with `K_vˢ` gives a `K`-embedding
  -- `jK` of `L` in `K_vᵃˡᵍ`, which intertwines `σ` with the image of `τ` in `G_{K_v}`.
  let φ := separableClosureRingEquiv (v.adicCompletion K) (w.adicCompletion E) iota
  let jK : L →ₐ[K] AlgebraicClosure (v.adicCompletion K) :=
    { ((separableClosure _ (AlgebraicClosure (v.adicCompletion K))).val.toRingHom.comp
        (φ.toRingHom.comp j.toRingHom)) with
      commutes' := fun k ↦ by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_ofClass, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, RingEquiv.toRingHom_eq_coe]
        have hk : algebraMap E (w.adicCompletion E) (algebraMap K E k) =
            algebraMap (v.adicCompletion K) (w.adicCompletion E)
              (algebraMap K (v.adicCompletion K) k) := by
          rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        rw [IsScalarTower.algebraMap_apply K E L, AlgHom.commutes,
          IsScalarTower.algebraMap_apply E (w.adicCompletion E)
            (SeparableClosure (w.adicCompletion E)), hk,
          separableClosureRingEquiv_algebraMap, AlgHom.commutes,
          IsScalarTower.algebraMap_apply K (v.adicCompletion K)
            (AlgebraicClosure (v.adicCompletion K))]
        exact AlgHom.commutes _ _ }
  -- By construction, `jK` is `j` followed by `φ` and the inclusion `K_vˢ ⊆ K_vᵃˡᵍ`.
  have hjK (z : L) : jK z = (φ (j z) : AlgebraicClosure (v.adicCompletion K)) := rfl
  rw [decompositionRestrict_mk
      (((separableClosure _ (AlgebraicClosure _)).val.restrictScalars E).comp j) τ σ
      fun x ↦ by
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, IntermediateField.coe_val, hσ]
        exact coe_absoluteGaloisGroupRestrictEquiv_apply _ τ (j x),
    Abelianization.map_of]
  refine decompositionRestrict_mk jK _ _ fun x ↦ ?_
  rw [hjK, hjK, AlgEquiv.restrictScalarsHom_apply, AlgEquiv.restrictScalars_apply, hσ,
    ← absoluteGaloisGroupExtend_apply_separableClosureRingEquiv]
  exact coe_absoluteGaloisGroupRestrictEquiv_apply _ _ (φ (j x))

end Normal

/-! ### Comparison with finite local reciprocity -/

variable {K L} [NumberField L] [IsGalois K L]

section Decomposition

variable (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- **The local Artin symbol is finite local reciprocity at a place above `v`.** For `L/K` Galois
and a finite place `w` of `L` above `v`, the local Artin symbol at `v` of `x ∈ K_vˣ` is the image
of its norm residue symbol in `Gal(L_w/K_v)^ab` under the identification of `Gal(L_w/K_v)` with
the decomposition group of `w` (`IsDedekindDomain.HeightOneSpectrum.decompositionEquiv`). -/
theorem localArtinAt_eq_map_normResidue (x : (v.adicCompletion K)ˣ) :
    localArtinAt K L v x =
      Abelianization.map ((MulAction.stabilizer Gal(L/K) w.asIdeal).subtype.comp
          (HeightOneSpectrum.decompositionEquiv v w).symm.toMonoidHom)
        (normResidue (v.adicCompletion K) (w.adicCompletion L)
          (x : (v.adicCompletion K)ˣ ⧸ normGroup (v.adicCompletion K) (w.adicCompletion L))) := by
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (artinMap (v.adicCompletion K) x)
  let ι : w.adicCompletion L →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K) :=
    IsSepClosed.lift
  -- `ρ ∈ Gal(L_w/K_v)` is the restriction of `τ`, and `σ` the element of the decomposition group
  -- of `w` acting on `L_w` as `ρ`.
  set ρ := ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) τ)
  set σ := (HeightOneSpectrum.decompositionEquiv v w).symm ρ
  rw [normResidue_mk _ _ ι, artinMap_restrict _ _ ι x τ hτ, toMul_ofMul, Abelianization.map_of]
  let j : L →ₐ[K] AlgebraicClosure (v.adicCompletion K) :=
    (((separableClosure (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))).val.comp
      ι).restrictScalars K).comp (IsScalarTower.toAlgHom K L (w.adicCompletion L))
  refine localArtinAt_eq_of_mk_eq_artinMap v τ hτ j (σ : Gal(L/K)) fun y ↦ ?_
  have hσ : HeightOneSpectrum.decompositionHom v w σ = ρ :=
    (congrFun (HeightOneSpectrum.coe_decompositionEquiv v w) σ).symm.trans
      ((HeightOneSpectrum.decompositionEquiv v w).apply_symm_apply ρ)
  simp only [j, AlgHom.comp_apply, AlgHom.restrictScalars_apply, IsScalarTower.coe_toAlgHom']
  rw [← HeightOneSpectrum.decompositionHom_algebraMap (v := v) σ y, hσ,
    ι.restrictNormalHom_commutes]
  exact coe_absoluteGaloisGroupRestrictEquiv_apply _ τ _

/-- **Local norms have trivial local Artin symbol.** For `L/K` Galois and `w` a finite place of
`L` above `v`, the norms from `L_w` lie in the kernel of the local Artin symbol at `v`. -/
theorem normGroup_le_ker_localArtinAt :
    normGroup (v.adicCompletion K) (w.adicCompletion L) ≤ (localArtinAt K L v).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, localArtinAt_eq_map_normResidue v w,
    (QuotientGroup.eq_one_iff x).2 hx, map_one, map_one]

/-- **The image of the local Artin symbol is the decomposition group.** For `L/K` Galois and `w`
a finite place of `L` above `v`, the local Artin symbols at `v` are exactly the classes in
`Gal(L/K)^ab` of the elements of the decomposition group of `w`. -/
theorem range_localArtinAt :
    (localArtinAt K L v).range =
      (MulAction.stabilizer Gal(L/K) w.asIdeal).map Abelianization.of := by
  set φ := (MulAction.stabilizer Gal(L/K) w.asIdeal).subtype.comp
    (HeightOneSpectrum.decompositionEquiv v w).symm.toMonoidHom
  -- The local Artin symbol factors as `K_vˣ ↠ K_vˣ ⧸ N(L_wˣ) ≃ Gal(L_w/K_v)^ab → Gal(L/K)^ab`.
  have h : localArtinAt K L v = ((Abelianization.map φ).comp
      (normResidue (v.adicCompletion K) (w.adicCompletion L)).toMonoidHom).comp
        (QuotientGroup.mk' _) :=
    MonoidHom.ext (localArtinAt_eq_map_normResidue v w)
  -- `Abelianization G` is the quotient of `G` by its commutator subgroup.
  have hof : Function.Surjective
      (Abelianization.of (G := Gal(w.adicCompletion L/v.adicCompletion K))) :=
    QuotientGroup.mk_surjective
  -- On `Gal(L_w/K_v)`, abelianizing after `φ` is the same as abelianizing before it.
  have hmap : (Abelianization.map φ).comp Abelianization.of = Abelianization.of.comp φ :=
    MonoidHom.ext (Abelianization.map_of φ)
  calc (localArtinAt K L v).range = (Abelianization.map φ).range := by
        rw [h, MonoidHom.range_comp_of_surjective _ _ (QuotientGroup.mk'_surjective _),
          MonoidHom.range_comp_of_surjective _ _ (normResidue _ _).surjective]
    _ = (Abelianization.of.comp φ).range := by
        rw [← hmap, MonoidHom.range_comp_of_surjective _ _ hof]
    _ = (MulAction.stabilizer Gal(L/K) w.asIdeal).map Abelianization.of := by
        rw [MonoidHom.range_comp, MonoidHom.range_comp_of_surjective _ _
          (HeightOneSpectrum.decompositionEquiv v w).symm.surjective, Subgroup.range_subtype]

/-- **For an abelian extension, the kernel of the local Artin symbol is the local norm group.**
If `Gal(L/K)` is commutative and `w` is a finite place of `L` above `v`, then `x ∈ K_vˣ` has
trivial local Artin symbol at `v` exactly when it is a norm from `L_w`. -/
theorem localArtinAt_eq_one_iff_mem_normGroup [IsMulCommutative Gal(L/K)]
    (x : (v.adicCompletion K)ˣ) :
    localArtinAt K L v x = 1 ↔ x ∈ normGroup (v.adicCompletion K) (w.adicCompletion L) := by
  set φ := (MulAction.stabilizer Gal(L/K) w.asIdeal).subtype.comp
    (HeightOneSpectrum.decompositionEquiv v w).symm.toMonoidHom
  -- `Gal(L_w/K_v)^ab → Gal(L/K)^ab` is injective: `Gal(L/K)` is commutative, so it is its own
  -- abelianization, and `Gal(L_w/K_v)` embeds in it as the decomposition group.
  have hφ : ∀ z, Abelianization.map φ z = 1 → z = 1 := fun z ↦ by
    induction z using QuotientGroup.induction_on with
    | H ρ =>
      intro h
      have h' : φ ρ = 1 := Abelianization.of_injective <| by
        rwa [← Abelianization.map_of, map_one]
      have hρ : ρ = 1 := (HeightOneSpectrum.decompositionEquiv v w).symm.injective <|
        Subtype.ext (by simpa [φ] using h')
      rw [hρ]
      exact map_one (Abelianization.of (G := Gal(w.adicCompletion L/v.adicCompletion K)))
  rw [localArtinAt_eq_map_normResidue v w]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [(QuotientGroup.eq_one_iff x).2 h, map_one, map_one]⟩
  rw [← QuotientGroup.eq_one_iff, ← (normResidue _ _).map_eq_one_iff]
  exact hφ _ h

/-! ### Unramified places -/

section Unramified

variable [Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal]

/-- **The local Artin symbol at an unramified place is a power of Frobenius.** If `w` is
unramified over `v` and `σ ∈ Gal(L/K)` is an arithmetic Frobenius at `w`, then the local Artin
symbol at `v` of `x ∈ K_vˣ` is the class of `σ` raised to the normalized valuation of `x`. -/
theorem localArtinAt_eq_of_isArithFrobAt {σ : Gal(L/K)} (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal)
    (x : (v.adicCompletion K)ˣ) :
    localArtinAt K L v x =
      Abelianization.of σ ^ (normalizedValuation (v.adicCompletion K) x).toAdd := by
  have : IsUnramified (v.adicCompletion K) (w.adicCompletion L) :=
    HeightOneSpectrum.isUnramified_adicCompletion_of_isUnramifiedAt v w
  -- Under the decomposition-group identification `σ` is the local Frobenius of `L_w/K_v`.
  have hfrob : (HeightOneSpectrum.decompositionEquiv v w).symm
      (frobeniusAlgEquiv (K := v.adicCompletion K) (L := w.adicCompletion L)) =
        ⟨σ, hσ.mem_stabilizer⟩ :=
    (HeightOneSpectrum.decompositionEquiv v w).symm_apply_eq.2 <|
      (HeightOneSpectrum.decompositionHom_eq_frobeniusAlgEquiv v w hσ).symm.trans
        (congrFun (HeightOneSpectrum.coe_decompositionEquiv v w) _).symm
  rw [localArtinAt_eq_map_normResidue v w, normResidue_mk _ _ IsSepClosed.lift,
    localArtinMap_eq_frobenius_pow_valuation]
  simp [hfrob]

/-- **A uniformizer has Frobenius as local Artin symbol** at a place unramified in `L`. -/
theorem localArtinAt_uniformizer_eq_of_isArithFrobAt {σ : Gal(L/K)}
    (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal) {π : (v.adicCompletion K)ˣ}
    (hπ : IsUniformizer (v.adicCompletion K) π) :
    localArtinAt K L v π = Abelianization.of σ := by
  rw [localArtinAt_eq_of_isArithFrobAt v w hσ, (isUniformizer_def π).1 hπ, toAdd_ofAdd,
    zpow_one]

include w in
/-- **Units have trivial local Artin symbol** at a place `v` below a place `w` of `L` unramified
over it. -/
theorem localArtinAt_eq_one_of_normalizedValuation_eq_one {u : (v.adicCompletion K)ˣ}
    (hu : normalizedValuation (v.adicCompletion K) u = 1) : localArtinAt K L v u = 1 := by
  obtain ⟨σ, hσ⟩ := NumberField.exists_isArithFrobAt K w.asIdeal w.ne_bot
  rw [localArtinAt_eq_of_isArithFrobAt v w hσ, hu, toAdd_one, zpow_zero]

end Unramified

end Decomposition

/-! ### Abelian extensions -/

/-- **At an unramified place of an abelian extension, the local Artin symbol is the Artin
automorphism of the ideal-theoretic Artin map** raised to the normalized valuation: the local
Artin symbol at `v` of `x ∈ K_vˣ` is `artinElement hab v hur ^ v(x)`. -/
theorem localArtinAt_eq_artinElement_zpow (hab : ∀ σ τ : Gal(L/K), Commute σ τ)
    (v : HeightOneSpectrum (𝓞 K))
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (x : (v.adicCompletion K)ˣ) :
    localArtinAt K L v x =
      Abelianization.of (NumberFieldArithmetic.artinElement hab v.asIdeal hur) ^
        (normalizedValuation (v.adicCompletion K) x).toAdd := by
  obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
  have := hur w.asIdeal
  exact localArtinAt_eq_of_isArithFrobAt _ w
    (NumberFieldArithmetic.isArithFrobAt_artinElement hab _ hur w.asIdeal) x

end TauCeti.ClassFieldTheory

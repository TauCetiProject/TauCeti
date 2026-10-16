/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.GeometricArtinMap
public import TauCeti.Topology.Algebra.Group.Profinite.Completion
import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.Existence
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup

/-!
# Injectivity of the absolute local Artin map and the profinite completion of `Kˣ`

Let `K` be a nonarchimedean local field of characteristic zero, for instance a finite extension
of `ℚ_p`. Local existence (`localExistence`) makes every subgroup of finite index of `Kˣ` a norm
subgroup, and this file draws its two consequences for the absolute local Artin map
`artinMap K : Kˣ →* G_K^ab`.

* **The profinite completion.** Since `G_K^ab` is profinite, `artinMap K` extends uniquely to a
  continuous homomorphism `profiniteCompletionArtinMap K` on the profinite completion `(Kˣ)^`. It
  is surjective for every local field, as `artinMap K` has dense image. In characteristic zero it
  is injective: a subgroup `H` of finite index is a norm subgroup, hence the preimage of an open
  subgroup `U` of `G_K^ab` (`exists_openSubgroup_artinMap_mem_iff`), and the `H`-coordinate of an
  element of `(Kˣ)^` is read off its image in `G_K^ab ⧸ U`. So it is an isomorphism of
  topological groups `profiniteCompletionArtinEquiv K : (Kˣ)^ ≃ₜ* G_K^ab`.
* **Injectivity** (`injective_artinMap`). Since `Kˣ` is residually finite
  (`TauCeti.residuallyFinite_units`), it embeds in `(Kˣ)^`, so `artinMap K` is injective as the
  restriction of the injective `profiniteCompletionArtinMap K`; so is its geometric normalization
  (`injective_geometricArtinMap`).

Neither statement is claimed in characteristic `p`: existence is only proved there for subgroups
of index prime to `p`, all of which contain the pro-`p` group of principal units.

## Main definitions

* `TauCeti.ClassFieldTheory.profiniteCompletionArtinMap`: the continuous extension of the absolute
  local Artin map to the profinite completion of `Kˣ`.
* `TauCeti.ClassFieldTheory.profiniteCompletionArtinEquiv`: in characteristic zero, the resulting
  isomorphism of topological groups `(Kˣ)^ ≃ₜ* G_K^ab`.

## Main results

* `TauCeti.ClassFieldTheory.injective_artinMap`: in characteristic zero the absolute local Artin
  map is injective.
* `TauCeti.ClassFieldTheory.injective_geometricArtinMap`: in characteristic zero the geometric
  local Artin map is injective.
* `TauCeti.ClassFieldTheory.surjective_profiniteCompletionArtinMap` and
  `TauCeti.ClassFieldTheory.injective_profiniteCompletionArtinMap`: the extension to the profinite
  completion is surjective, and in characteristic zero injective.

## References

* J.-P. Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VI, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter V, §1.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### The profinite completion of `Kˣ` -/

/-- The **absolute local Artin map on the profinite completion** of `Kˣ`: the unique continuous
extension of `artinMap K` to `(Kˣ)^`, which exists because `G_K^ab` is profinite. In
characteristic zero it is an isomorphism (`profiniteCompletionArtinEquiv`). -/
def profiniteCompletionArtinMap :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Kˣ) →ₜ*
      Field.absoluteGaloisGroupAbelianization K :=
  (ProfiniteCompletion.continuousMonoidHomEquiv Kˣ _).symm (artinMap K)

/-- On the image of `Kˣ` in its profinite completion, `profiniteCompletionArtinMap K` is the
absolute local Artin map. -/
@[simp]
theorem profiniteCompletionArtinMap_etaFn (x : Kˣ) :
    profiniteCompletionArtinMap K (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of Kˣ) x) =
      artinMap K x :=
  ProfiniteCompletion.continuousMonoidHomEquiv_symm_apply_etaFn _ _ _ _

/-- The extension of the absolute local Artin map to the profinite completion of `Kˣ` is
surjective: its image is compact, hence closed, and contains the dense image of `artinMap K`. -/
theorem surjective_profiniteCompletionArtinMap :
    Function.Surjective (profiniteCompletionArtinMap K) :=
  ProfiniteCompletion.surjective_continuousMonoidHom_of_denseRange _ _ <| by
    simpa using denseRange_artinMap K

/-- In characteristic zero the extension of the absolute local Artin map to the profinite
completion of `Kˣ` is injective: every subgroup of finite index of `Kˣ` is a norm subgroup
(`localExistence`), hence the preimage of an open subgroup of `G_K^ab`
(`exists_openSubgroup_artinMap_mem_iff`). -/
theorem injective_profiniteCompletionArtinMap [CharZero K] :
    Function.Injective (profiniteCompletionArtinMap K) := by
  refine ProfiniteCompletion.injective_continuousMonoidHom_of_forall_exists_nhds_one_comap_le _ _
    fun H ↦ ?_
  obtain ⟨V, hV⟩ := localExistence H.toSubgroup
  obtain ⟨U, hU⟩ := exists_openSubgroup_artinMap_mem_iff K V
  refine ⟨U, U.mem_nhds_one, fun x hx ↦ ?_⟩
  rw [SetLike.mem_coe, profiniteCompletionArtinMap_etaFn, hU, hV] at hx
  exact hx

/-- **The absolute local Artin map is injective in characteristic zero**, in particular for a
finite extension of `ℚ_p`: it is the composite of the injective extension
`profiniteCompletionArtinMap K` with the map of `Kˣ` into its profinite completion, which is
injective because `Kˣ` is residually finite. -/
theorem injective_artinMap [CharZero K] : Function.Injective (artinMap K) := by
  have hη := (ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite
    (G := GrpCat.of Kˣ)).2 inferInstance
  intro x y hxy
  rw [← profiniteCompletionArtinMap_etaFn, ← profiniteCompletionArtinMap_etaFn] at hxy
  exact hη (injective_profiniteCompletionArtinMap K hxy)

/-- The geometric local Artin map is injective in characteristic zero, in particular for a finite
extension of `ℚ_p`. -/
theorem injective_geometricArtinMap [CharZero K] : Function.Injective (geometricArtinMap K) :=
  fun x y h ↦ injective_artinMap K <| by simpa using h

/-- **The profinite completion of `Kˣ` is `G_K^ab`.** In characteristic zero, in particular for a
finite extension of `ℚ_p`, the absolute local Artin map extends to an isomorphism of topological
groups from the profinite completion of `Kˣ` onto `G_K^ab`
(`profiniteCompletionArtinEquiv_apply`). -/
def profiniteCompletionArtinEquiv [CharZero K] :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Kˣ) ≃ₜ*
      Field.absoluteGaloisGroupAbelianization K :=
  -- The `show`s state each proof argument at the type its constructor expects, so that
  -- `profiniteCompletionArtinEquiv_apply` follows by rewriting with the constructors' lemmas.
  .mk' (Continuous.homeoOfEquivCompactToT2 (f := .ofBijective _
      (show Function.Bijective _ from ⟨injective_profiniteCompletionArtinMap K,
        surjective_profiniteCompletionArtinMap K⟩))
      (show Continuous _ from map_continuous (profiniteCompletionArtinMap K)))
    (show ∀ _ _, _ from map_mul (profiniteCompletionArtinMap K))

/-- The isomorphism `(Kˣ)^ ≃ G_K^ab` is the extension of the absolute local Artin map. -/
@[simp]
theorem profiniteCompletionArtinEquiv_apply [CharZero K]
    (c : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Kˣ)) :
    profiniteCompletionArtinEquiv K c = profiniteCompletionArtinMap K c := by
  rw [profiniteCompletionArtinEquiv, ContinuousMulEquiv.coe_mk', ← Homeomorph.coe_toEquiv,
    Continuous.toEquiv_homeoOfEquivCompactToT2, Equiv.ofBijective_apply]

end TauCeti.ClassFieldTheory

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.Topology.Algebra.Group.Profinite.Completion
import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.Existence
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup

/-!
# Injectivity of the absolute local Artin map and the profinite completion of `Kˣ`

Let `K` be a nonarchimedean local field of characteristic zero, for instance a finite extension
of `ℚ_p`. Local existence (`localExistence`) makes every subgroup of finite index of `Kˣ` a norm
subgroup, and this file draws its two consequences for the absolute local Artin map
`artinMap K : Kˣ →* G_K^ab`.

* **Injectivity** (`injective_artinMap`). The kernel of `artinMap K` is the intersection of all norm
  subgroups (`ker_artinMap_eq_iInf`), so it lies in every subgroup of finite index of `Kˣ`. These
  intersect in `1`, because `Kˣ` is residually finite (`TauCeti.residuallyFinite_units`).
* **The profinite completion.** Since `G_K^ab` is profinite, `artinMap K` extends uniquely to a
  continuous homomorphism `profiniteCompletionArtinMap K` on the profinite completion `(Kˣ)^`. It
  is surjective for every local field, as `artinMap K` has dense image. In characteristic zero it
  is injective: a subgroup `H` of finite index is a norm subgroup, hence the preimage of an open
  subgroup `U` of `G_K^ab` (`exists_openSubgroup_artinMap_mem_iff`), and the `H`-coordinate of an
  element of `(Kˣ)^` is read off its image in `G_K^ab ⧸ U`. So it is an isomorphism of
  topological groups `profiniteCompletionArtinEquiv K : (Kˣ)^ ≃ₜ* G_K^ab`.

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

/-- **The absolute local Artin map is injective in characteristic zero**, in particular for a
finite extension of `ℚ_p`: its kernel lies in every norm subgroup (`ker_artinMap_eq_iInf`), hence,
by local existence, in every subgroup of finite index of the residually finite group `Kˣ`. -/
theorem injective_artinMap [CharZero K] : Function.Injective (artinMap K) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hker : x ∈ ⨅ V : OpenNormalSubgroup (AbsoluteGaloisGroup K), localNormSubgroup K V := by
    rw [← ker_artinMap_eq_iInf]
    exact hx
  refine Group.residuallyFinite_iff_forall_finiteIndex.1 inferInstance x fun N _ ↦ ?_
  obtain ⟨V, hV⟩ := localExistence N
  exact hV ▸ Subgroup.mem_iInf.1 hker V

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

/-- **The profinite completion of `Kˣ` is `G_K^ab`.** In characteristic zero, in particular for a
finite extension of `ℚ_p`, the absolute local Artin map extends to an isomorphism of topological
groups from the profinite completion of `Kˣ` onto `G_K^ab`
(`profiniteCompletionArtinEquiv_apply`). -/
def profiniteCompletionArtinEquiv [CharZero K] :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Kˣ) ≃ₜ*
      Field.absoluteGaloisGroupAbelianization K :=
  .mk' ((map_continuous (profiniteCompletionArtinMap K)).homeoOfEquivCompactToT2
    (f := .ofBijective _ ⟨injective_profiniteCompletionArtinMap K,
      surjective_profiniteCompletionArtinMap K⟩))
    (map_mul (profiniteCompletionArtinMap K))

/-- The isomorphism `(Kˣ)^ ≃ G_K^ab` is the extension of the absolute local Artin map. -/
@[simp]
theorem profiniteCompletionArtinEquiv_apply [CharZero K]
    (c : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Kˣ)) :
    profiniteCompletionArtinEquiv K c = profiniteCompletionArtinMap K c :=
  by
    let e := Equiv.ofBijective (profiniteCompletionArtinMap K)
      ⟨injective_profiniteCompletionArtinMap K, surjective_profiniteCompletionArtinMap K⟩
    let he : Continuous e := by
      apply Continuous.congr (map_continuous (profiniteCompletionArtinMap K))
      exact fun x ↦ (Equiv.ofBijective_apply _ _ x).symm
    let h := he.homeoOfEquivCompactToT2
    calc
      profiniteCompletionArtinEquiv K c =
          ContinuousMulEquiv.mk' h (map_mul (profiniteCompletionArtinMap K)) c := by rfl
      _ = h c := congrFun (ContinuousMulEquiv.coe_mk' h _) c
      _ = e c := by
        change h.toEquiv c = e c
        dsimp only [h]
        rw [Continuous.toEquiv_homeoOfEquivCompactToT2]
      _ = profiniteCompletionArtinMap K c := Equiv.ofBijective_apply _ _ _

end TauCeti.ClassFieldTheory

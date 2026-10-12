/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Quotient
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Basic
import TauCeti.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.TateCohomology.NegativeCorestriction
public import TauCeti.RepresentationTheory.RelativeNorm
import TauCeti.RepresentationTheory.Coinvariants

/-!
# Restriction in negative Tate degrees and maps in the two low degrees

Let `G` be a finite group, `H ≤ G` a subgroup and `M` a `G`-representation. In every Tate degree
there are a restriction map `tateCohomology M n ⟶ tateCohomology (Rep.res H.subtype M) n` and a
corestriction map back, and the composite of the two is multiplication by the index `[G : H]`.
In the degrees where the Tate complex is the complex of inhomogeneous cochains — that is, in
degrees `≥ 1` — restriction is the ordinary restriction of group cohomology, and in the degrees
where it is the complex of inhomogeneous chains — degrees `≤ -2` — corestriction is the ordinary
change-of-group map of group homology, both of which Mathlib already provides. Degrees `0` and
`-1` are the two degrees where the Tate complex is neither, being glued there by the norm map:
degree `0` is `Mᴳ / N_G M` and degree `-1` is `ker N_G / I_G M`.

This file supplies restriction in degrees at most `-2` by transporting the homological transfer
through Mathlib's comparison with group homology. It also supplies all four maps in degrees `0`
and `-1`, using the identifications of
`TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree`. Restriction in degree `0` and
corestriction in degree `-1` are induced by inclusions of representatives, `Mᴳ ⊆ Mᴴ` and
`ker N_G ⊇ ker N_H`. The other two are induced by the relative norm and the relative transfer of
`H` in `G` of `TauCeti.RepresentationTheory.RelativeNorm`: corestriction in degree `0` is the
relative norm `N_{G/H} : Mᴴ → Mᴳ`, and restriction in degree `-1` is the relative transfer, which
carries `ker N_G` into `ker N_H` and `I_G M` into `I_H M`.

In both degrees the composite of restriction and corestriction is multiplication by `[G : H]`,
because the relative norm is `[G : H] • ·` on `Mᴳ` and the relative transfer is `[G : H] • ·`
modulo `I_G M`. In degrees at most `-2` the same identity is corestriction after transfer in group
homology, `TauCeti.groupHomology.transfer_comp_map_subtype_id`, with corestriction taken from
`TauCeti.RepresentationTheory.Homological.TateCohomology.NegativeCorestriction`.

With trivial integral coefficients, the restriction of `Rep.trivial ℤ G ℤ` to `H` is the trivial
representation of `H`, and the identity of `ℤ` is a compatible pair between the two; the resulting
comparison `trivialResIso` reads the order of degree-zero and the vanishing of degree-one Tate
cohomology of `Rep.trivial ℤ H ℤ` on the restricted representation.

## Main definitions

* `TauCeti.TateCohomology.H0Res`, `TauCeti.TateCohomology.H0Cor`: restriction and corestriction
  in degree `0`.
* `TauCeti.TateCohomology.HNegOneRes`, `TauCeti.TateCohomology.HNegOneCor`: restriction and
  corestriction in degree `-1`.
* `TauCeti.TateCohomology.negSuccRes`: restriction in degree `-(n+1)` for `n > 0`.
* `TauCeti.TateCohomology.HNegTwoRes`: the degree-`-2` specialization.
* `TauCeti.TateCohomology.trivialResIso`: Tate cohomology of the trivial integral representation
  of a subgroup, as Tate cohomology of the restricted trivial representation.
* `TauCeti.TateCohomology.resTrivialTateHZeroOne`: the class of `1` in degree-zero Tate
  cohomology of the restricted trivial integral representation; it generates, and is killed by
  the order of the subgroup.

## Main results

* `TauCeti.TateCohomology.negSuccRes_comp_negSuccIso_hom`: negative restriction agrees with
  homological transfer through `TauCeti.TateCohomology.negSuccIso`.
* `TauCeti.TateCohomology.H0π_comp_H0Res`, `TauCeti.TateCohomology.H0π_comp_H0Cor`,
  `TauCeti.TateCohomology.HNegOneπ_comp_HNegOneRes`,
  `TauCeti.TateCohomology.HNegOneπ_comp_HNegOneCor`: the effect of each map on the class of a
  representative.
* `TauCeti.TateCohomology.HNegTwoRes_def`: restriction in degree `-2` is the transfer in first
  group homology, transported through Mathlib's comparison with group homology.
* `TauCeti.TateCohomology.HNegTwoRes_comp_isoGroupHomology_hom`: this comparison commutes
  with restriction and homological transfer.
* `TauCeti.TateCohomology.H0Res_comp_H0Cor`,
  `TauCeti.TateCohomology.HNegOneRes_comp_HNegOneCor` and
  `TauCeti.TateCohomology.negSuccRes_comp_negSuccCor`: corestriction after restriction is
  multiplication by the index.
* `TauCeti.TateCohomology.natCard_tateCohomology_zero_res_trivial_int_eq_card`,
  `TauCeti.TateCohomology.isZero_tateCohomology_one_res_trivial_int`: degree-zero Tate cohomology
  of the restricted trivial integral representation has the order of the subgroup, and its
  degree-one Tate cohomology vanishes.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6 and Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9 and Chapter VI, §5.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter II, §1.
-/

public noncomputable section

universe u

open CategoryTheory LinearMap Rep Representation

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G] (M : Rep R G)
  (H : Subgroup G)

attribute [local instance] Subgroup.fintypeOfFinite Subgroup.fintypeQuotientOfFiniteIndex

section Negative

/-- Restriction to a subgroup in Tate degree `-(n+1)`, for `n > 0`. Through Mathlib's
negative-degree comparison, this is the transfer in `n`th group homology. -/
def negSuccRes (n : ℕ) [NeZero n] :
    tateCohomology M (Int.negSucc n) ⟶
      tateCohomology (Rep.res H.subtype M) (Int.negSucc n) :=
  (_root_.TateCohomology.isoGroupHomology (Int.negSucc n) n (Int.negSucc_eq n)).hom.app M ≫
    TauCeti.groupHomology.transfer M H n ≫
      (_root_.TateCohomology.isoGroupHomology (Int.negSucc n) n (Int.negSucc_eq n)).inv.app
        (Rep.res H.subtype M)

/-- Negative-degree Tate restriction is the homological transfer through
`TauCeti.TateCohomology.negSuccIso`. -/
@[reassoc (attr := simp)]
theorem negSuccRes_comp_negSuccIso_hom (n : ℕ) [NeZero n] :
    negSuccRes M H n ≫ (negSuccIso (Rep.res H.subtype M) n).hom =
      (negSuccIso M n).hom ≫ TauCeti.groupHomology.transfer M H n := by
  simp only [negSuccIso_hom]
  -- Cancelling the comparison isomorphism against the definition, rather than rewriting with
  -- `Iso.inv_hom_id_app`: the objects involved appear both as `tateCohomology` and as values of
  -- `tateCohomologyFunctor`, so the rewrite does not match syntactically, while this equation
  -- holds by `rfl`.
  exact (Iso.eq_comp_inv _).1 (by rfl)

/-- Restriction to a subgroup in degree `-2` Tate cohomology. Under the comparison with first
group homology, this is the homological transfer. -/
def HNegTwoRes :
    tateCohomology M (-2) ⟶ tateCohomology (Rep.res H.subtype M) (-2) :=
  negSuccRes M H 1

/-- Degree-`-2` restriction is the degree-one instance of negative restriction. -/
theorem HNegTwoRes_eq_negSuccRes : HNegTwoRes M H = negSuccRes M H 1 :=
  (rfl)

/-- Restriction in Tate degree `-2` is the transfer in first group homology, transported through
Mathlib's negative-degree comparison `TateCohomology.isoGroupHomology`. -/
theorem HNegTwoRes_def :
    HNegTwoRes M H =
      (_root_.TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).hom.app M ≫
        TauCeti.groupHomology.transfer M H 1 ≫
          (_root_.TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).inv.app
            (Rep.res H.subtype M) := by
  rfl

/-- Restriction in degree `-2` commutes with the comparison to first group homology. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem HNegTwoRes_comp_isoGroupHomology_hom :
    HNegTwoRes M H ≫ (_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app
      (Rep.res H.subtype M) =
      (_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app M ≫
        TauCeti.groupHomology.transfer M H 1 :=
  (Iso.eq_comp_inv ((_root_.TateCohomology.isoGroupHomology (-2) 1 rfl).app _)).1
    ((HNegTwoRes_def _ _).trans (Category.assoc _ _ _).symm)

/-- Restriction followed by corestriction is multiplication by the index, in every Tate degree
`-(n+1)` with `n > 0`. -/
@[reassoc, elementwise]
theorem negSuccRes_comp_negSuccCor (n : ℕ) [NeZero n] :
    negSuccRes M H n ≫ negSuccCor M H.subtype n =
      H.index • 𝟙 (tateCohomology M (Int.negSucc n)) := by
  -- Through the comparison with group homology this is `cor ∘ transfer = [G : H]`. Squeezed:
  -- the bare `simp` is several times slower.
  rw [← cancel_mono (negSuccIso M n).hom]
  simp only [Category.assoc, negSuccCor_comp_negSuccIso_hom, negSuccRes_comp_negSuccIso_hom_assoc,
    TauCeti.groupHomology.transfer_comp_map_subtype_id, Linear.comp_smul, Linear.smul_comp,
    Category.comp_id, Category.id_comp]

end Negative

section Zero

private theorem h0_res_le :
    (range M.ρ.norm).submoduleOf M.ρ.invariants ≤
      Submodule.comap
        (Submodule.inclusion
          (Representation.invariants_le_invariants_comp_subtype (ρ := M.ρ) (H := H)))
        ((range (Rep.res H.subtype M).ρ.norm).submoduleOf (Rep.res H.subtype M).ρ.invariants) :=
  fun _ hx => Representation.range_norm_le_range_norm_comp_subtype (H := H) hx

private theorem h0_cor_le :
    (range (Rep.res H.subtype M).ρ.norm).submoduleOf (Rep.res H.subtype M).ρ.invariants ≤
      Submodule.comap (Representation.relNormInvariants M.ρ H)
        ((range M.ρ.norm).submoduleOf M.ρ.invariants) := by
  rintro ⟨x, hx⟩ ⟨y, rfl⟩
  exact ⟨y, by simp [Representation.relNorm_norm_apply]⟩

/-- Restriction to a subgroup in degree zero Tate cohomology, induced by the inclusion of the
invariants `Mᴳ ⊆ Mᴴ`. -/
def H0Res : tateCohomology M 0 ⟶ tateCohomology (Rep.res H.subtype M) 0 :=
  (H0IsoNormQuotient M).hom ≫
    ModuleCat.ofHom (Submodule.mapQ _ _ _ (h0_res_le M H)) ≫
    (H0IsoNormQuotient (Rep.res H.subtype M)).inv

/-- Corestriction from a subgroup in degree zero Tate cohomology, induced by the relative norm
`Mᴴ → Mᴳ`. -/
def H0Cor : tateCohomology (Rep.res H.subtype M) 0 ⟶ tateCohomology M 0 :=
  (H0IsoNormQuotient (Rep.res H.subtype M)).hom ≫
    ModuleCat.ofHom (Submodule.mapQ _ _ _ (h0_cor_le M H)) ≫
    (H0IsoNormQuotient M).inv

/-- Restriction in degree zero sends the class of a `G`-invariant element to the class of the
same element, viewed as an `H`-invariant element. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem H0π_comp_H0Res :
    H0π M ≫ H0Res M H =
      ModuleCat.ofHom (Submodule.inclusion
        (Representation.invariants_le_invariants_comp_subtype (ρ := M.ρ) (H := H))) ≫
        H0π (Rep.res H.subtype M) := by
  rw [H0Res]
  exact ModuleCat.comp_conj_mapQ _ _ (H0π_comp_H0IsoNormQuotient_hom _)
    (H0π_comp_H0IsoNormQuotient_hom _) _ _

/-- Corestriction in degree zero sends the class of an `H`-invariant element to the class of its
relative norm. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem H0π_comp_H0Cor :
    H0π (Rep.res H.subtype M) ≫ H0Cor M H =
      ModuleCat.ofHom (Representation.relNormInvariants M.ρ H) ≫ H0π M := by
  rw [H0Cor]
  exact ModuleCat.comp_conj_mapQ _ _ (H0π_comp_H0IsoNormQuotient_hom _)
    (H0π_comp_H0IsoNormQuotient_hom _) _ _

/-- Corestriction of the restriction of a degree-zero class is the index multiple of it. -/
theorem H0Cor_comp_H0Res_apply (x : tateCohomology M 0) :
    H0Cor M H (H0Res M H x) = H.index • x := by
  induction x using H0_induction_on with
  | h y =>
    rw [H0π_comp_H0Res_apply, H0π_comp_H0Cor_apply, ← map_nsmul]
    congr 1
    ext
    simpa using M.ρ.relNorm_apply_of_forall_apply_eq (H := H)
      ((Representation.mem_invariants _ _).1 y.2)

/-- Restriction followed by corestriction is multiplication by the index, in degree zero. -/
theorem H0Res_comp_H0Cor :
    H0Res M H ≫ H0Cor M H = H.index • 𝟙 (tateCohomology M 0) := by
  ext x
  simpa using H0Cor_comp_H0Res_apply M H x

end Zero

section NegOne

private theorem hNegOne_res_le :
    (Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm) ≤
      Submodule.comap (Representation.relTransferKerNorm M.ρ H)
        ((Coinvariants.ker (Rep.res H.subtype M).ρ).submoduleOf
          (ker (Rep.res H.subtype M).ρ.norm)) :=
  fun _ hx => by
    simpa only [Submodule.mem_comap, Submodule.submoduleOf, Submodule.subtype_apply,
      Representation.coe_relTransferKerNorm] using Representation.relTransfer_mem_coinvariantsKer hx

private theorem hNegOne_cor_le :
    (Coinvariants.ker (Rep.res H.subtype M).ρ).submoduleOf (ker (Rep.res H.subtype M).ρ.norm) ≤
      Submodule.comap
        (Submodule.inclusion
          (Representation.ker_norm_comp_subtype_le_ker_norm (ρ := M.ρ) (H := H)))
        ((Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) :=
  fun _ hx => M.ρ.coinvariantsKer_comp_le H.subtype hx

/-- Restriction to a subgroup in degree `-1` Tate cohomology, induced by the relative transfer. -/
def HNegOneRes :
    tateCohomology M (-1) ⟶ tateCohomology (Rep.res H.subtype M) (-1) :=
  (HNegOneIsoNormKernelQuotient M).hom ≫
    ModuleCat.ofHom (Submodule.mapQ _ _ _ (hNegOne_res_le M H)) ≫
    (HNegOneIsoNormKernelQuotient (Rep.res H.subtype M)).inv

/-- Corestriction from a subgroup in degree `-1` Tate cohomology, induced by the inclusion of the
kernel of the norm of `H` in the kernel of the norm of `G`. -/
def HNegOneCor :
    tateCohomology (Rep.res H.subtype M) (-1) ⟶ tateCohomology M (-1) :=
  (HNegOneIsoNormKernelQuotient (Rep.res H.subtype M)).hom ≫
    ModuleCat.ofHom (Submodule.mapQ _ _ _ (hNegOne_cor_le M H)) ≫
    (HNegOneIsoNormKernelQuotient M).inv

/-- Restriction in degree `-1` sends the class of a norm-zero element to the class of its
relative transfer. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem HNegOneπ_comp_HNegOneRes :
    HNegOneπ M ≫ HNegOneRes M H =
      ModuleCat.ofHom (Representation.relTransferKerNorm M.ρ H) ≫
        HNegOneπ (Rep.res H.subtype M) := by
  rw [HNegOneRes]
  exact ModuleCat.comp_conj_mapQ _ _ (HNegOneπ_comp_HNegOneIsoNormKernelQuotient_hom _)
    (HNegOneπ_comp_HNegOneIsoNormKernelQuotient_hom _) _ _

/-- Corestriction in degree `-1` sends the class of a norm-zero element to the class of the same
element. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem HNegOneπ_comp_HNegOneCor :
    HNegOneπ (Rep.res H.subtype M) ≫ HNegOneCor M H =
      ModuleCat.ofHom (Submodule.inclusion
        (Representation.ker_norm_comp_subtype_le_ker_norm (ρ := M.ρ) (H := H))) ≫
        HNegOneπ M := by
  rw [HNegOneCor]
  exact ModuleCat.comp_conj_mapQ _ _ (HNegOneπ_comp_HNegOneIsoNormKernelQuotient_hom _)
    (HNegOneπ_comp_HNegOneIsoNormKernelQuotient_hom _) _ _

/-- Corestriction of the restriction of a degree `-1` class is the index multiple of it. -/
theorem HNegOneCor_comp_HNegOneRes_apply (x : tateCohomology M (-1)) :
    HNegOneCor M H (HNegOneRes M H x) = H.index • x := by
  induction x using HNegOne_induction_on with
  | h y =>
    rw [HNegOneπ_comp_HNegOneRes_apply, HNegOneπ_comp_HNegOneCor_apply, ← map_nsmul,
      HNegOneπ_eq_iff]
    simp [Submodule.submoduleOf, Representation.relTransfer_sub_index_nsmul_mem]

/-- Restriction followed by corestriction is multiplication by the index, in degree `-1`. -/
theorem HNegOneRes_comp_HNegOneCor :
    HNegOneRes M H ≫ HNegOneCor M H = H.index • 𝟙 (tateCohomology M (-1)) := by
  ext x
  simpa using HNegOneCor_comp_HNegOneRes_apply M H x

/-- **Tate restriction in degree `-1` is natural in the coefficient representation.** -/
@[reassoc]
theorem HNegOneRes_natural {N : Rep R G} (f : M ⟶ N) :
    (tateCohomologyFunctor (-1)).map f ≫ HNegOneRes N H =
      HNegOneRes M H ≫ (tateCohomologyFunctor (-1)).map ((Rep.resFunctor H.subtype).map f) := by
  let g := (Rep.resFunctor H.subtype).map f
  let hφ : M.ρ.IsIntertwiningMap
      (N.ρ.comp ((MulEquiv.refl G : G ≃* G) : G →* G)) f.hom.toLinearMap :=
    ⟨fun g v ↦ Rep.hom_comm_apply f g v⟩
  let hφH : (Rep.res H.subtype M).ρ.IsIntertwiningMap
      ((Rep.res H.subtype N).ρ.comp ((MulEquiv.refl H : H ≃* H) : H →* H))
      g.hom.toLinearMap := ⟨fun x v ↦ Rep.hom_comm_apply g x v⟩
  -- Along the identity of the group, the Tate map of a compatible pair is coefficient
  -- functoriality (`map_refl`), so `HNegOneπ_comp_map` computes both coefficient maps.
  have hmap : HNegOneπ M ≫ (tateCohomologyFunctor (-1)).map f =
      ModuleCat.ofHom (mapKerNorm hφ) ≫ HNegOneπ N :=
    (map_refl hφ (-1)).symm ▸ HNegOneπ_comp_map hφ
  have hmapH : HNegOneπ (Rep.res H.subtype M) ≫ (tateCohomologyFunctor (-1)).map g =
      ModuleCat.ofHom (mapKerNorm hφH) ≫ HNegOneπ (Rep.res H.subtype N) :=
    (map_refl hφH (-1)).symm ▸ HNegOneπ_comp_map hφH
  -- The relative transfer commutes with the coefficient map on norm kernels.
  have htransfer : ModuleCat.ofHom (mapKerNorm hφ) ≫
        ModuleCat.ofHom (Representation.relTransferKerNorm N.ρ H) =
      ModuleCat.ofHom (Representation.relTransferKerNorm M.ρ H) ≫
        ModuleCat.ofHom (mapKerNorm hφH) := by
    ext x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    rw [Representation.coe_relTransferKerNorm, mapKerNorm_apply_coe,
      mapKerNorm_apply_coe, Representation.coe_relTransferKerNorm,
      Representation.relTransfer_apply, Representation.relTransfer_apply, map_sum]
    exact Finset.sum_congr rfl fun q _ ↦ (Rep.hom_comm_apply f q.out⁻¹ x).symm
  rw [← cancel_epi (HNegOneπ M), reassoc_of% hmap, HNegOneπ_comp_HNegOneRes,
    HNegOneπ_comp_HNegOneRes_assoc, reassoc_of% htransfer, hmapH]

end NegOne

section TrivialInt

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
/-- The identity of `ℤ` intertwines the trivial representation of a subgroup `S` of `G` with the
restriction to `S` of the trivial representation of `G`. -/
theorem isIntertwiningMap_trivial_res (S : Subgroup G) :
    (Rep.trivial ℤ S ℤ).ρ.IsIntertwiningMap
      ((Rep.res S.subtype (Rep.trivial ℤ G ℤ)).ρ.comp ((MulEquiv.refl S : S ≃* S) : S →* S))
      (LinearEquiv.refl ℤ ℤ) :=
  Rep.isIntertwiningMap_trivial ℤ _

/-- Tate cohomology of the trivial integral representation of a subgroup `S` of `G`, identified
with Tate cohomology of the restriction to `S` of the trivial integral representation of `G`. -/
def trivialResIso (S : Subgroup G) (n : ℤ) :
    tateCohomology (Rep.trivial ℤ S ℤ) n ≅
      tateCohomology (Rep.res S.subtype (Rep.trivial ℤ G ℤ)) n :=
  mapIso (e := MulEquiv.refl S) (e' := LinearEquiv.refl ℤ ℤ) (isIntertwiningMap_trivial_res S) n

/-- The comparison `trivialResIso` is the Tate map attached to the compatible pair
`isIntertwiningMap_trivial_res`. -/
@[simp]
theorem trivialResIso_hom (S : Subgroup G) (n : ℤ) :
    (trivialResIso S n).hom =
      map (e := MulEquiv.refl S) (isIntertwiningMap_trivial_res S) n := by
  rw [trivialResIso, mapIso_hom]

/-- The class of `1 ∈ ℤ` in degree-zero Tate cohomology of the restriction to `S` of the trivial
integral representation of `G`. -/
def resTrivialTateHZeroOne (S : Subgroup G) :
    tateCohomology (Rep.res S.subtype (Rep.trivial ℤ G ℤ)) 0 :=
  H0π _ ⟨1, fun _ ↦ rfl⟩

/-- The class of `1` is the degree-zero projection of the invariant `1`. -/
theorem resTrivialTateHZeroOne_def (S : Subgroup G) :
    resTrivialTateHZeroOne S = H0π _ ⟨1, fun _ ↦ rfl⟩ :=
  (rfl)

/-- Every degree-zero class of the restricted trivial integral representation is an integer
multiple of the class of `1`. -/
theorem exists_zsmul_resTrivialTateHZeroOne_eq (S : Subgroup G)
    (x : tateCohomology (Rep.res S.subtype (Rep.trivial ℤ G ℤ)) 0) :
    ∃ n : ℤ, n • resTrivialTateHZeroOne S = x := by
  induction x using H0_induction_on with
  | h y =>
    refine ⟨(y : ℤ), ?_⟩
    rw [resTrivialTateHZeroOne_def, ← map_zsmul]
    congr 1
    exact Subtype.ext (by simp)

/-- The order of the subgroup kills the class of `1`. -/
theorem natCard_zsmul_resTrivialTateHZeroOne (S : Subgroup G) :
    (Nat.card S : ℤ) • resTrivialTateHZeroOne S = 0 := by
  rw [resTrivialTateHZeroOne_def, ← map_zsmul]
  refine (H0π_eq_zero_iff _).2 ⟨1, ?_⟩
  simp [Representation.norm, Nat.card_eq_fintype_card]

/-- Degree-zero Tate cohomology of the restricted trivial integral representation has the order
of the subgroup. -/
theorem natCard_tateCohomology_zero_res_trivial_int_eq_card (S : Subgroup G) :
    Nat.card (tateCohomology (Rep.res S.subtype (Rep.trivial ℤ G ℤ)) 0) = Nat.card S :=
  (Nat.card_congr (trivialResIso S 0).toLinearEquiv.toEquiv).symm.trans
    (natCard_tateCohomology_zero_trivial_int_eq_card S)

/-- Degree-one Tate cohomology of the restricted trivial integral representation vanishes: it is
`H¹(S, ℤ) = Hom(S, ℤ) = 0`. -/
theorem isZero_tateCohomology_one_res_trivial_int (S : Subgroup G) :
    Limits.IsZero (tateCohomology (Rep.res S.subtype (Rep.trivial ℤ G ℤ)) 1) :=
  ((TauCeti.groupCohomology.isZero_H1_of_isTrivial (Rep.trivial ℤ S ℤ)).of_iso
    ((TateCohomology.isoGroupCohomology 1).app (Rep.trivial ℤ S ℤ))).of_iso
      (trivialResIso S 1).symm

end TrivialInt

end TauCeti.TateCohomology

/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
public import TauCeti.RepresentationTheory.RelativeNorm

/-!
# Restriction and corestriction to a subgroup in degrees `0` and `-1` of Tate cohomology

Let `G` be a finite group, `H ≤ G` a subgroup and `M` a `G`-representation. In every Tate degree
there are a restriction map `tateCohomology M n ⟶ tateCohomology (Rep.res H.subtype M) n` and a
corestriction map back, and the composite of the two is multiplication by the index `[G : H]`.
In the degrees where the Tate complex is the complex of inhomogeneous cochains — that is, in
degrees `≥ 1` — restriction is the ordinary restriction of group cohomology, and in the degrees
where it is the complex of inhomogeneous chains — degrees `≤ -2` — corestriction is the ordinary
change-of-group map of group homology, both of which Mathlib already provides. Degrees `0` and
`-1` are the two degrees where the Tate complex is neither, being glued there by the norm map:
degree `0` is `Mᴳ / N_G M` and degree `-1` is `ker N_G / I_G M`.

This file supplies all four maps in exactly those two degrees, using the identifications of
`TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree`. Restriction in degree `0` and
corestriction in degree `-1` are induced by inclusions of representatives, `Mᴳ ⊆ Mᴴ` and
`ker N_G ⊇ ker N_H`. The other two are induced by the relative norm and the relative transfer of
`H` in `G` of `TauCeti.RepresentationTheory.RelativeNorm`: corestriction in degree `0` is the
relative norm `N_{G/H} : Mᴴ → Mᴳ`, and restriction in degree `-1` is the relative transfer, which
carries `ker N_G` into `ker N_H` and `I_G M` into `I_H M`.

In both degrees the composite of restriction and corestriction is multiplication by `[G : H]`,
because the relative norm is `[G : H] • ·` on `Mᴳ` and the relative transfer is `[G : H] • ·`
modulo `I_G M`.

## Main definitions

* `TauCeti.TateCohomology.H0Res`, `TauCeti.TateCohomology.H0Cor`: restriction and corestriction
  in degree `0`.
* `TauCeti.TateCohomology.HNegOneRes`, `TauCeti.TateCohomology.HNegOneCor`: restriction and
  corestriction in degree `-1`.

## Main results

* `TauCeti.TateCohomology.H0π_comp_H0Res`, `TauCeti.TateCohomology.H0π_comp_H0Cor`,
  `TauCeti.TateCohomology.HNegOneπ_comp_HNegOneRes`,
  `TauCeti.TateCohomology.HNegOneπ_comp_HNegOneCor`: the effect of each map on the class of a
  representative.
* `TauCeti.TateCohomology.H0Res_comp_H0Cor` and
  `TauCeti.TateCohomology.HNegOneRes_comp_HNegOneCor`: corestriction after restriction is
  multiplication by the index.

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

/-- A subgroup of a finite group is a finite type. -/
noncomputable local instance fintypeSubgroup : Fintype H := Fintype.ofFinite H

/-- The quotient of a finite group by a subgroup is a finite type. -/
noncomputable local instance fintypeQuotientGroup : Fintype (G ⧸ H) :=
  H.fintypeQuotientOfFiniteIndex

/-- A map conjugated from `Submodule.mapQ p₁ p₂ f` along identifications `e₁`, `e₂` of two
objects with the quotients sends the class `π₁ x` of a representative to the class `π₂ (f x)`. -/
private theorem comp_conj_mapQ {X₁ X₂ : Type u} [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂]
    [Module R X₂] {p₁ : Submodule R X₁} {p₂ : Submodule R X₂} {A₁ A₂ : ModuleCat.{u} R}
    (e₁ : A₁ ≅ ModuleCat.of R (X₁ ⧸ p₁)) (e₂ : A₂ ≅ ModuleCat.of R (X₂ ⧸ p₂))
    {π₁ : ModuleCat.of R X₁ ⟶ A₁} {π₂ : ModuleCat.of R X₂ ⟶ A₂}
    (hπ₁ : π₁ ≫ e₁.hom = ModuleCat.ofHom p₁.mkQ) (hπ₂ : π₂ ≫ e₂.hom = ModuleCat.ofHom p₂.mkQ)
    (f : X₁ →ₗ[R] X₂) (hf : p₁ ≤ p₂.comap f) :
    π₁ ≫ e₁.hom ≫ ModuleCat.ofHom (p₁.mapQ p₂ f hf) ≫ e₂.inv = ModuleCat.ofHom f ≫ π₂ := by
  rw [← cancel_mono e₂.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, reassoc_of% hπ₁, hπ₂,
    ← ModuleCat.ofHom_comp, Submodule.mapQ_mkQ]

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
  refine ⟨y, ?_⟩
  simpa using (Representation.relNorm_norm_apply (ρ := M.ρ) (H := H) y).symm

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
  exact comp_conj_mapQ _ _ (H0π_comp_H0IsoNormQuotient_hom _)
    (H0π_comp_H0IsoNormQuotient_hom _) _ _

/-- Corestriction in degree zero sends the class of an `H`-invariant element to the class of its
relative norm. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem H0π_comp_H0Cor :
    H0π (Rep.res H.subtype M) ≫ H0Cor M H =
      ModuleCat.ofHom (Representation.relNormInvariants M.ρ H) ≫ H0π M := by
  rw [H0Cor]
  exact comp_conj_mapQ _ _ (H0π_comp_H0IsoNormQuotient_hom _)
    (H0π_comp_H0IsoNormQuotient_hom _) _ _

/-- Corestriction of the restriction of a degree-zero class is the index multiple of it. -/
theorem H0Cor_comp_H0Res_apply (x : tateCohomology M 0) :
    H0Cor M H (H0Res M H x) = H.index • x := by
  induction x using H0_induction_on with
  | h y =>
    rw [H0π_comp_H0Res_apply, H0π_comp_H0Cor_apply, ← map_nsmul]
    congr 1
    ext
    simpa using Representation.relNorm_apply_of_mem_invariants (H := H) y.2

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
  fun x hx => by
    rw [Submodule.mem_comap, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      Representation.coe_relTransferKerNorm]
    exact Representation.relTransfer_mem_coinvariantsKer (H := H) hx

private theorem hNegOne_cor_le :
    (Coinvariants.ker (Rep.res H.subtype M).ρ).submoduleOf (ker (Rep.res H.subtype M).ρ.norm) ≤
      Submodule.comap
        (Submodule.inclusion
          (Representation.ker_norm_comp_subtype_le_ker_norm (ρ := M.ρ) (H := H)))
        ((Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) :=
  fun _ hx => Representation.coinvariantsKer_comp_subtype_le (H := H) hx

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
  exact comp_conj_mapQ _ _ (HNegOneπ_comp_HNegOneIsoNormKernelQuotient_hom _)
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
  exact comp_conj_mapQ _ _ (HNegOneπ_comp_HNegOneIsoNormKernelQuotient_hom _)
    (HNegOneπ_comp_HNegOneIsoNormKernelQuotient_hom _) _ _

/-- Corestriction of the restriction of a degree `-1` class is the index multiple of it. -/
theorem HNegOneCor_comp_HNegOneRes_apply (x : tateCohomology M (-1)) :
    HNegOneCor M H (HNegOneRes M H x) = H.index • x := by
  induction x using HNegOne_induction_on with
  | h y =>
    rw [HNegOneπ_comp_HNegOneRes_apply, HNegOneπ_comp_HNegOneCor_apply, ← map_nsmul,
      HNegOneπ_eq_iff]
    refine Submodule.mem_comap.2 ?_
    simpa using Representation.relTransfer_sub_index_nsmul_mem (ρ := M.ρ) (H := H) (y : M.V)

/-- Restriction followed by corestriction is multiplication by the index, in degree `-1`. -/
theorem HNegOneRes_comp_HNegOneCor :
    HNegOneRes M H ≫ HNegOneCor M H = H.index • 𝟙 (tateCohomology M (-1)) := by
  ext x
  simpa using HNegOneCor_comp_HNegOneRes_apply M H x

end NegOne

end TauCeti.TateCohomology

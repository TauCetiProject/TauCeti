/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.AbelianLayer

/-!
# Upward closure of local norm subgroups

Let `K` be a nonarchimedean local field. A subgroup `N ≤ Kˣ` containing the norm subgroup of a
finite Galois extension is itself the norm subgroup of a finite **abelian** extension
(`exists_abelianLayer_localNormSubgroup_eq_of_le`). This is the reciprocity half of local
existence: once every open subgroup of finite index is known to contain some norm subgroup, it is
a norm subgroup.

The proof is by local reciprocity alone. By norm limitation the given layer may be replaced by its
maximal abelian sublayer `U`, whose Artin map `Kˣ → G_K ⧸ U` is surjective with kernel the norm
subgroup. The image of `N` is a subgroup of the abelian group `G_K ⧸ U`, and its preimage in
`G_K` is an open normal subgroup `W ⊇ U`, an abelian layer whose norm subgroup is computed in the
refinement `U ≤ W` by `localNormSubgroup_eq_comap_ker`: it is `N` enlarged by the kernel of the
Artin map, which is `N` again.

## Main results

* `TauCeti.ClassFieldTheory.exists_abelianLayer_localNormSubgroup_eq_of_le`: a subgroup of `Kˣ`
  containing a local norm subgroup is the norm subgroup of an abelian layer.
* `TauCeti.ClassFieldTheory.exists_abelianLayer_localNormSubgroup_eq_of_normGroup_le`: the same
  for a subgroup containing the norm group of any finite separable extension.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter XIV,
  §6.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open NormalLayer

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Upward closure of local norm subgroups.** For a nonarchimedean local field `K`, a subgroup
of `Kˣ` containing the norm subgroup of the finite Galois extension cut out by `V` is the norm
subgroup of a finite abelian extension. -/
theorem exists_abelianLayer_localNormSubgroup_eq_of_le
    {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)} {N : Subgroup Kˣ}
    (h : localNormSubgroup K V ≤ N) :
    ∃ W : OpenNormalSubgroup (AbsoluteGaloisGroup K),
      W.IsAbelianClassFieldLayer ∧ localNormSubgroup K W = N := by
  -- replace `V` by its maximal abelian sublayer `U`, which has the same norm subgroup
  set U := V.maximalAbelianLayer
  have hU : U.IsAbelianClassFieldLayer := V.isAbelianClassFieldLayer_maximalAbelianLayer
  rw [← localNormSubgroup_maximalAbelianLayer] at h
  have : IsMulCommutative (AbsoluteGaloisGroup K ⧸ U.toSubgroup) :=
    (U.isAbelianClassFieldLayer_iff_isMulCommutative).1 hU
  -- the Artin map of `U`, read in `G_K ⧸ U`, and the image of `N` there
  let ψ : Kˣ →* AbsoluteGaloisGroup K ⧸ U.toSubgroup :=
    (galOfOpenNormalEquiv U : (ofOpenNormal U).Gal →* _).comp (localAbelianArtinHom K hU)
  have hψ : ψ.ker = localNormSubgroup K U := by
    rw [MonoidHom.ker_mulEquiv_comp, ker_localAbelianArtinHom]
  let H : Subgroup (AbsoluteGaloisGroup K ⧸ U.toSubgroup) := N.map ψ
  -- its preimage in `G_K` is an open normal subgroup containing `U`
  have hUW : U.toSubgroup ≤ H.comap (QuotientGroup.mk' U.toSubgroup) := fun g hg ↦ by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
    exact H.one_mem
  let W : OpenNormalSubgroup (AbsoluteGaloisGroup K) :=
    { toSubgroup := H.comap (QuotientGroup.mk' U.toSubgroup)
      isOpen' := Subgroup.isOpen_mono hUW U.isOpen
      isNormal' := inferInstance }
  -- the order on open normal subgroups is inclusion of the underlying subgroups
  have hle : U ≤ W := hUW
  refine ⟨W, hU.mono hle, ?_⟩
  -- the kernel of `G_K ⧸ U → G_K ⧸ W` is the image of `H` in the Galois group of `U`
  have hker :
      (LayerRefinement.ofOpenNormal hle).galHom.ker = H.comap (galOfOpenNormalEquiv U) := by
    ext γ
    induction γ using QuotientGroup.induction_on with
    | H w =>
      rw [MonoidHom.mem_ker, LayerRefinement.galHom_mk_eq_one_iff, top_ofOpenNormal,
        Subgroup.mem_comap, MonoidHom.coe_ofClass, galOfOpenNormalEquiv_mk]
      -- membership in `W` is membership of the class in `H`
      exact Iff.rfl
  rw [localNormSubgroup_eq_comap_ker hU hle, hker, Subgroup.comap_comap, Subgroup.comap_map_eq,
    hψ, sup_eq_left.2 h]

/-- **Upward closure from a finite separable extension.** For a nonarchimedean local field `K`, a
subgroup of `Kˣ` containing the norm group `N_{M/K}(Mˣ)` of a finite separable extension `M/K`
is the norm subgroup of a finite abelian extension. The extension `M` need not be Galois, nor lie
in the separable closure: the normal closure of an embedding of `M` into `Kˢ` is a finite Galois
extension with a smaller norm group. -/
theorem exists_abelianLayer_localNormSubgroup_eq_of_normGroup_le {M : Type*} [Field M]
    [Algebra K M] [FiniteDimensional K M] [Algebra.IsSeparable K M] {N : Subgroup Kˣ}
    (h : normGroup K M ≤ N) :
    ∃ W : OpenNormalSubgroup (AbsoluteGaloisGroup K),
      W.IsAbelianClassFieldLayer ∧ localNormSubgroup K W = N := by
  -- the normal closure of `M` in `Kˢ` is the class field of some `V`
  let E := IntermediateField.normalClosure K M (SeparableClosure K)
  obtain ⟨V, hV⟩ := (exists_classField_eq_iff E).2 ⟨inferInstance, inferInstance⟩
  refine exists_abelianLayer_localNormSubgroup_eq_of_le (V := V) (le_trans ?_ h)
  rw [localNormSubgroup_def]
  exact AlgHom.normGroup_le_normGroup ((IntermediateField.equivOfEq hV.symm).toAlgHom.comp
    ((normalClosure.algHomEquiv K M (SeparableClosure K)).symm IsSepClosed.lift))

end TauCeti.ClassFieldTheory

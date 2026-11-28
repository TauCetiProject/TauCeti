/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormSubgroup
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
import TauCeti.GroupTheory.Abelianization.Basic

/-!
# The absolute global Artin map

For a number field `K`, `absoluteGlobalArtinMap` maps the idele class group `C_K` to the
topological abelianization of the absolute Galois group. It specializes
`ClassFormation.absoluteArtinMap` to the global class formation. Its finite restrictions
recover `globalArtinMap` and, for abelian extensions, `ideleClassArtinMap`.
Continuity follows from the openness of the idele-class norm subgroups
(`isOpen_globalNormSubgroup`) and the open subgroup basis of a profinite group.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, §5.
* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, §2.4.
-/

public noncomputable section

open NumberField

namespace TauCeti.ClassFieldTheory

/-- The absolute global Artin map `C_K → G_K^ab` of a number field, obtained from the inverse
limit of finite Artin maps in the global class formation. -/
def absoluteGlobalArtinMap (K : Type) [Field K] [NumberField K] :
    IdeleClassGroup (𝓞 K) K →* Field.absoluteGaloisGroupAbelianization K :=
  (absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr.toMonoidHom.comp
    (MonoidHom.toAdditive.symm
      ((globalClassFormation K).absoluteArtinMap.comp (globalGroundEquiv K).toAddMonoidHom))

-- Do not put this expansion in simp. It hides the absolute symbol from the restriction API.
/-- The absolute global Artin symbol is the symbol of the global class formation, transported
from the separable closure to Mathlib's algebraic closure. -/
theorem absoluteGlobalArtinMap_apply (K : Type) [Field K] [NumberField K]
    (c : IdeleClassGroup (𝓞 K) K) :
    absoluteGlobalArtinMap K c =
      (absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr
        ((globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (.ofMul c))).toMul := (rfl)

/-- On the separable-closure model of `G_K^ab`, the absolute global Artin symbol is the
symbol of the global class formation. -/
@[simp]
theorem absoluteGlobalArtinMap_restrict (K : Type) [Field K] [NumberField K]
    (c : IdeleClassGroup (𝓞 K) K) :
    (absoluteGaloisGroupRestrictEquiv K).topologicalAbelianizationCongr
        (absoluteGlobalArtinMap K c) =
      ((globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (.ofMul c))).toMul := by
  rw [absoluteGlobalArtinMap_apply, ← ContinuousMulEquiv.topologicalAbelianizationCongr_symm,
    ContinuousMulEquiv.apply_symm_apply]

/-- The kernel of the absolute global Artin map modulo an open normal subgroup of `G_K^ab`
is the norm subgroup of a finite Galois layer. -/
theorem _root_.OpenNormalSubgroup.exists_ker_mk'_comp_absoluteGlobalArtinMap_eq {K : Type}
    [Field K] [NumberField K] (U : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    ∃ V : OpenNormalSubgroup (AbsoluteGaloisGroup K),
      ((QuotientGroup.mk' U.toSubgroup).comp (absoluteGlobalArtinMap K)).ker =
        globalNormSubgroup K V := by
  let e := (absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr
  obtain ⟨V, hV⟩ := (globalClassFormation K).exists_absoluteArtinMap_mem_iff
    (U.toOpenSubgroup.comap e.toMonoidHom (map_continuous e))
  refine ⟨V, Subgroup.ext fun c ↦ ?_⟩
  -- Triviality in the finite quotient is membership in the open subgroup.
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  rw [absoluteGlobalArtinMap_apply, mem_globalNormSubgroup_iff, ← hV]
  simpa only [e, OpenSubgroup.mem_toSubgroup, ContinuousMulEquiv.toMulEquiv_eq_coe,
    MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, ContinuousMulEquiv.coe_toMulEquiv] using
    (OpenSubgroup.mem_comap (H := U.toOpenSubgroup) (f := e.toMonoidHom)
      (hf := map_continuous e)).symm

variable (K : Type) [Field K] [NumberField K]

/-- The absolute global Artin map of a number field is continuous. -/
theorem continuous_absoluteGlobalArtinMap : Continuous (absoluteGlobalArtinMap K) := by
  refine continuous_iff_forall_continuous_mk.mpr fun U ↦ ?_
  obtain ⟨V, hV⟩ := U.exists_ker_mk'_comp_absoluteGlobalArtinMap_eq
  let f := (QuotientGroup.mk' U.toSubgroup).comp (absoluteGlobalArtinMap K)
  have hopen : IsOpen (f.ker : Set (IdeleClassGroup (𝓞 K) K)) :=
    hV ▸ isOpen_globalNormSubgroup K V
  simpa only [f, MonoidHom.coe_comp, Function.comp_def, QuotientGroup.mk'_apply] using
    f.continuous_of_isOpen_ker hopen

/-- The absolute global Artin map kills the connected component of the identity of `C_K`. -/
theorem absoluteGlobalArtinMap_eq_one_of_mem_connectedComponent {c : IdeleClassGroup (𝓞 K) K}
    (hc : c ∈ connectedComponent (1 : IdeleClassGroup (𝓞 K) K)) :
    absoluteGlobalArtinMap K c = 1 := by
  have hmem : absoluteGlobalArtinMap K c ∈
      absoluteGlobalArtinMap K '' connectedComponent (1 : IdeleClassGroup (𝓞 K) K) :=
    Set.mem_image_of_mem _ hc
  rwa [(continuous_absoluteGlobalArtinMap K).image_connectedComponent_eq_singleton,
    Set.mem_singleton_iff, map_one] at hmem

section Finite

open scoped IsMulCommutative

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]

/-- Restricting a representative of an absolute global Artin symbol to a finite Galois extension
gives the finite Artin symbol in the abelianization of its Galois group. -/
theorem globalArtinMap_eq_of_mk_eq_absoluteGlobalArtinMap [IsGalois K L]
    (ι : L →ₐ[K] SeparableClosure K)
    {c : IdeleClassGroup (𝓞 K) K} {g : Field.absoluteGaloisGroup K}
    (hg : (g : Field.absoluteGaloisGroupAbelianization K) = absoluteGlobalArtinMap K c) :
    globalArtinMap K L ι (.ofMul c) =
      .ofMul (Group.Abelianization.of
        (ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K g))) := by
  apply globalArtinMap_eq_of_mk_eq_absoluteArtinMap K L ι
  -- Transport the representative back to the separable closure used by the class formation.
  rw [← ContinuousMulEquiv.topologicalAbelianizationCongr_mk, hg,
    absoluteGlobalArtinMap_restrict, ofMul_toMul]

/-- Over a finite abelian extension, the restriction of an absolute global Artin symbol is the
finite Artin symbol in the Galois group itself. -/
theorem ideleClassArtinMap_eq_of_mk_eq_absoluteGlobalArtinMap [IsAbelianGalois K L]
    (ι : L →ₐ[K] SeparableClosure K) {c : IdeleClassGroup (𝓞 K) K} {g : Field.absoluteGaloisGroup K}
    (hg : (g : Field.absoluteGaloisGroupAbelianization K) = absoluteGlobalArtinMap K c) :
    ideleClassArtinMap K L c = ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K g) := by
  apply Group.Abelianization.of_injective
  rw [of_ideleClassArtinMap K L ι,
    globalArtinMap_eq_of_mk_eq_absoluteGlobalArtinMap K L ι hg, toMul_ofMul]

end Finite

end TauCeti.ClassFieldTheory

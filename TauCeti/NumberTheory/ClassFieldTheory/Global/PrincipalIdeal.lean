/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.ClassFormation
import TauCeti.NumberTheory.ClassFieldTheory.Formation.PrincipalIdeal

/-!
# The idelic consequence of Furtwängler's theorem

Let `L/F` be a finite Galois extension of number fields inside a separable closure, and let `E`
be its maximal abelian subextension. Every idele class of `F`, extended to `E`, is a norm of an
idele class of `L` (`ideleClassExtension_mem_range_ideleClassNormMap_commutator`). Equivalently,
the extension map `C_F → C_E` becomes trivial modulo `N_{L/E}(C_L)`.

The fields are identified by the finite layers of the global formation: if `Lay` represents
`L/F`, then the ground field of `Lay.subgroupLayer (commutator Lay.Gal)` is `E`. No abelianity
of `L/F` or unramifiedness is needed. Inclusion of ground levels is extension of idele classes,
and the abstract principal ideal theorem for `globalClassFormation` makes its image a norm.

This is the norm-theoretic input to ideal principalization: applying it to the Hilbert class
field tower additionally requires identifying its maximal abelian subextension and identifying
the norm subgroup at its upper step with the trivial-modulus ray subgroup. The result here does
not assert that ideals principalize in the maximal abelian subextension of an arbitrary `L/F`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIII.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §7 (the principal ideal theorem).
-/

public section

open IntermediateField NumberField

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable {K : Type} [Field K] [NumberField K]

section Layer

variable {F E L : IntermediateField K (SeparableClosure K)}
  [NumberField F] [NumberField E] [NumberField L]
  [Algebra F E] [IsScalarTower F E (SeparableClosure K)]
  [Algebra E L] [IsScalarTower E L (SeparableClosure K)]

/-- **The idelic consequence of Furtwängler's theorem.** If `Lay` represents `L/F` and `E` is
its maximal abelian subextension, every idele class of `F`, extended to `E`, is a norm from `L`.
The field `E` is pinned as the fixed field of the preimage of the commutator subgroup of the
finite Galois group; no norm or principalization hypothesis is assumed. -/
theorem ideleClassExtension_mem_range_ideleClassNormMap_commutator
    (Lay : NormalLayer (AbsoluteGaloisGroup K))
    (hF : fixedField Lay.ground.toSubgroup = F)
    (hE : fixedField (Lay.subgroupLayer (commutator Lay.Gal)).ground.toSubgroup = E)
    (hL : fixedField Lay.top.toSubgroup = L) (c : IdeleClassGroup (𝓞 F) F) :
    ideleClassExtension F E c ∈ (ideleClassNormMap E L :
      IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 E) E).range := by
  let T := Lay.subgroupRestriction (commutator Lay.Gal)
  have h := (globalClassFormation K).groundInclusion_mem_normSubgroup_of_range_eq_commutator
    T (Lay.range_galHom_subgroupRestriction _) (ideleClassLevelEquiv hF (.ofMul c))
  rw [T.groundInclusion_ideleClassLevelEquiv hF hE] at h
  exact ((Lay.subgroupLayer (commutator Lay.Gal)).ideleClassLevelEquiv_mem_normSubgroup_iff
    hE (by rw [NormalLayer.top_subgroupLayer]; exact hL) _).mp h

end Layer

/-- **Idele classes of the base field become norms over the maximal abelian subextension.**
For the finite Galois extension cut out by `V`, with top field `L` and maximal abelian
subextension `E`, the image of `C_K → C_E` lies in `N_{L/E}(C_L)`. -/
theorem ideleClassExtension_mem_range_ideleClassNormMap_commutator_ofOpenNormal
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    {E L : IntermediateField K (SeparableClosure K)} [NumberField E] [NumberField L]
    [Algebra E L] [IsScalarTower E L (SeparableClosure K)]
    (hE : fixedField ((NormalLayer.ofOpenNormal V).subgroupLayer
      (commutator (NormalLayer.ofOpenNormal V).Gal)).ground.toSubgroup = E)
    (hL : fixedField (NormalLayer.ofOpenNormal V).top.toSubgroup = L)
    (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassExtension K E c ∈ (ideleClassNormMap E L :
      IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 E) E).range := by
  let B : IntermediateField K (SeparableClosure K) := ⊥
  let : NumberField B := .of_module_finite K B
  let : Algebra B E := (IntermediateField.inclusion bot_le).toRingHom.toAlgebra
  have : IsScalarTower B E (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hB : fixedField (NormalLayer.ofOpenNormal V).ground.toSubgroup = B := by
    rw [NormalLayer.ground_ofOpenNormal]
    exact fixedField_toSubgroup_top K
  have h := ideleClassExtension_mem_range_ideleClassNormMap_commutator
    (NormalLayer.ofOpenNormal V) hB hE hL (ideleClassExtension K B c)
  rwa [← MonoidHom.comp_apply, ideleClassExtension_comp] at h

end TauCeti.ClassFieldTheory

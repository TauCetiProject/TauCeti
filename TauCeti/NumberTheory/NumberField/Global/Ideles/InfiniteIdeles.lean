/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.InfiniteAdele
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.InfiniteGaloisAction
public import TauCeti.RepresentationTheory.Pi

/-!
# The infinite ideles as a Galois representation

Let `L/K` be an extension of number fields. The infinite ideles of `L` are the units
`L_∞ˣ = ∏_w L_wˣ` of its infinite adele ring, the product running over the infinite places `w` of
`L`. The automorphisms of `L/K` act on them through the Galois action on infinite adeles
(`TauCeti.GlobalNumberFields.infiniteAdeleGaloisAction`), which permutes the places of `L`.

Grouping the places of `L` by the infinite place `v` of `K` below them identifies the infinite
ideles, as an integral representation of `Aut(L/K)`, with the product over `v` of the units of the
semi-local algebras `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w`:

```text
L_∞ˣ ≅ ∏_v (K_v ⊗[K] L)ˣ
```

(`infiniteIdelesPiIso`). Each factor is coinduced from the units of a single completion
(`TauCeti.GlobalNumberFields.infiniteSemilocalUnitsCoindIso`), so this decomposition is how the
Tate cohomology of the infinite ideles reduces to the Galois cohomology of the archimedean local
fields. The infinite ideles are the archimedean factor of the `S`-ideles
`I_{L,S} = L_∞ˣ × ∏_{w ∈ S} L_wˣ × ∏_{w ∉ S} 𝒪_wˣ`.

## Main definitions

* `TauCeti.GlobalNumberFields.infiniteIdeleMulDistribMulAction`: the Galois action on the infinite
  ideles, an instance in the scope `AdeleGaloisAction`.
* `TauCeti.GlobalNumberFields.infiniteIdelesRep`: the infinite ideles of `L` as an integral
  representation of `Aut(L/K)`.
* `TauCeti.GlobalNumberFields.infiniteIdelesPiIso`: its decomposition as the product over the
  infinite places of `K` of the semi-local units.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

noncomputable section

open NumberField CategoryTheory
open scoped TensorProduct

namespace TauCeti.GlobalNumberFields

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- **The Galois action on infinite ideles**: `σ ∈ Aut(L/K)` acts on the units of the infinite
adele ring of `L` by the ring automorphism `infiniteAdeleGaloisAction K L σ`. It is a definition
rather than a global instance, available as an instance in the scope `AdeleGaloisAction`. -/
abbrev infiniteIdeleMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (InfiniteAdeleRing L)ˣ :=
  letI := MulSemiringAction.compHom (InfiniteAdeleRing L) (infiniteAdeleGaloisAction K L)
  Units.mulDistribMulActionRight

scoped[AdeleGaloisAction] attribute [instance]
  TauCeti.GlobalNumberFields.infiniteIdeleMulDistribMulAction

open scoped AdeleGaloisAction

variable {K L} in
/-- The Galois action on an infinite idele is the Galois action on the underlying infinite
adele. -/
theorem coe_infiniteIdele_smul (σ : L ≃ₐ[K] L) (x : (InfiniteAdeleRing L)ˣ) :
    ((σ • x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) = infiniteAdeleGaloisAction K L σ x :=
  (rfl)

/-- The infinite ideles of `L`, the units of its infinite adele ring, as an integral
representation of `Aut(L/K)`. -/
abbrev infiniteIdelesRep : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (InfiniteAdeleRing L)ˣ

variable [NumberField K] [NumberField L]

/-- The semi-local components of an infinite idele, as an isomorphism of groups
`L_∞ˣ ≃ ∏_v (K_v ⊗[K] L)ˣ`. -/
private def infiniteIdelesPiMulEquiv :
    (InfiniteAdeleRing L)ˣ ≃* ∀ v : InfinitePlace K, (v.Completion ⊗[K] L)ˣ :=
  (Units.mapEquiv (infiniteAdeleSemilocalEquiv K L).toMulEquiv).trans MulEquiv.piUnits

/-- **The infinite ideles are the product of the semi-local units.** As integral representations
of `Aut(L/K)`, the infinite ideles of `L` are the product over the infinite places `v` of `K` of
the units of `K_v ⊗[K] L`, by the semi-local components above each `v`. -/
def infiniteIdelesPiIso :
    infiniteIdelesRep K L ≅ Rep.pi fun v : InfinitePlace K ↦ infiniteSemilocalUnitsRep L v :=
  Rep.mkIso <| .mk (infiniteIdelesPiMulEquiv K L).toAdditive.toIntLinearEquiv fun σ ↦
    LinearMap.ext fun x ↦ funext fun v ↦ Additive.toMul.injective <| Units.ext <| by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Representation.pi_apply,
        Representation.ofMulDistribMulAction_apply_apply]
      exact infiniteAdeleSemilocalEquiv_infiniteAdeleGaloisAction σ x.toMul.1 v

variable {K L}

/-- The component at `v` of the image of an infinite idele under `infiniteIdelesPiIso` is its
semi-local component above `v`. -/
theorem coe_infiniteIdelesPiIso_hom_apply (x : Additive (InfiniteAdeleRing L)ˣ)
    (v : InfinitePlace K) :
    ((Additive.toMul ((infiniteIdelesPiIso K L).hom.hom x v) : (v.Completion ⊗[K] L)ˣ) :
      v.Completion ⊗[K] L) = infiniteAdeleSemilocalHom L v x.toMul :=
  infiniteAdeleSemilocalEquiv_apply _ v

end TauCeti.GlobalNumberFields

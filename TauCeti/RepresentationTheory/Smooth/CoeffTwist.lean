/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Smooth.Admissible
public import TauCeti.RepresentationTheory.Smooth.Category

/-!
# The twist of a smooth representation by a ring automorphism

Let `σ` be a ring automorphism of a commutative ring `A` (for instance `σ ∈ Aut(ℂ)`). The
`σ`-twist of an `A`-module `V` is the same additive group with `a` acting as `σ⁻¹(a)`; it is
`A ⊗_{A,σ} V`, through `a ⊗ v ↦ σ⁻¹(a) • v`. A representation `ρ` of `G` on `V` gives the
`σ`-twisted representation `ρ^σ` on it, with the same operators: they are additive and commute
with every `σ⁻¹(a)`. The twist keeps the stabilizer of every vector, the subrepresentations and the
invariants of every subgroup, so it preserves smoothness, admissibility and irreducibility, and
twisting by `σ` and then by `τ` is twisting by `σ.trans τ = τ ∘ σ`. On smooth representations it is
an autoequivalence of `SmoothRep A G`, with inverse the twist by `σ⁻¹`.

## Main definitions

* `TauCeti.CoeffTwist σ V`: the `A`-module `V` with `a` acting as `σ⁻¹(a)`, and
  `TauCeti.CoeffTwist.of σ V : V ≃+ CoeffTwist σ V` the identity map.
* `Representation.coeffTwist σ ρ`: the `σ`-twist `ρ^σ` of a representation.
* `TauCeti.SmoothRep.coeffTwist σ`: the `σ`-twist functor `SmoothRep A G ⥤ SmoothRep A G`.
* `TauCeti.SmoothRep.coeffTwistEquiv σ`: the `σ`-twist as an autoequivalence of `SmoothRep A G`,
  with inverse `coeffTwist σ.symm`.

## Main results

* `Representation.stabilizer_coeffTwist`: twisting keeps stabilizers, so `ρ^σ` is smooth when `ρ`
  is (`Representation.isSmooth_coeffTwist_iff`).
* `Representation.isAdmissible_coeffTwist_iff`: `ρ^σ` is admissible exactly when `ρ` is.
* `Representation.subrepresentationCoeffTwistOrderIso`: the subrepresentations of `ρ` and `ρ^σ`
  are the same subsets, so over a field `ρ^σ` is irreducible exactly when `ρ` is
  (`Representation.isIrreducible_coeffTwist_iff`).
* `TauCeti.SmoothRep.coeffTwistReflIso`, `TauCeti.SmoothRep.coeffTwistTransIso`: twisting by the
  identity is the identity functor, and twisting by `σ` then by `τ` is twisting by `σ.trans τ`.

## References

* J. Bernstein, *Le "centre" de Bernstein*, edited by P. Deligne, in *Représentations des groupes
  réductifs sur un corps local*, Hermann, 1984, §2.0, Generalization, p. 9.
-/

@[expose] public section

open CategoryTheory

universe w u v

namespace TauCeti

/-- The **`σ`-twist** of an `A`-module `V` by a ring automorphism `σ` of `A`: the additive group
`V`, on which `a ∈ A` acts as `σ⁻¹(a)`. It is `A ⊗_{A,σ} V` through `a ⊗ v ↦ σ⁻¹(a) • v`. -/
@[nolint unusedArguments]
def CoeffTwist {A : Type*} [CommRing A] (_σ : A ≃+* A) (V : Type*) : Type _ := V

namespace CoeffTwist

variable {A : Type*} [CommRing A] (σ : A ≃+* A) (V : Type*) [AddCommGroup V] [Module A V]

instance instAddCommGroup : AddCommGroup (CoeffTwist σ V) := inferInstanceAs (AddCommGroup V)

/-- `a ∈ A` acts on the `σ`-twist of `V` as `σ⁻¹(a)` acts on `V`. -/
instance instModule : Module A (CoeffTwist σ V) := Module.compHom V (σ.symm : A →+* A)

/-- The identity map of `V`, as an additive equivalence onto its `σ`-twist. -/
def of : V ≃+ CoeffTwist σ V := AddEquiv.refl V

variable {σ V}

/-- `a` acts on the `σ`-twist as `σ⁻¹(a)` acts on `V`. -/
theorem smul_of (a : A) (v : V) : a • of σ V v = of σ V (σ.symm a • v) :=
  (rfl)

/-- Moving `a • v` to the `σ`-twist turns `a` into `σ(a)`. -/
theorem of_smul (a : A) (v : V) : of σ V (a • v) = σ a • of σ V v := by
  rw [smul_of, RingEquiv.symm_apply_apply]

/-- `of σ V` as a `σ`-semilinear map. -/
def ofSemilinear : V →ₛₗ[(σ : A →+* A)] CoeffTwist σ V where
  __ := (of σ V).toAddMonoidHom
  map_smul' := of_smul

@[simp]
theorem ofSemilinear_apply (v : V) : ofSemilinear v = of σ V v :=
  (rfl)

/-- The inverse of `of σ V` as a `σ⁻¹`-semilinear map. -/
def toSemilinear : CoeffTwist σ V →ₛₗ[(σ.symm : A →+* A)] V where
  __ := (of σ V).symm.toAddMonoidHom
  map_smul' _ _ := (rfl)

@[simp]
theorem toSemilinear_of (v : V) : toSemilinear (of σ V v) = v :=
  (rfl)

omit [Module A V] in
/-- Every vector of the `σ`-twist comes from `V`. -/
@[elab_as_elim]
theorem induction {motive : CoeffTwist σ V → Prop} (h : ∀ v, motive (of σ V v))
    (x : CoeffTwist σ V) : motive x :=
  h ((of σ V).symm x)

end CoeffTwist

end TauCeti

namespace Representation

open TauCeti

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]
  (σ : A ≃+* A) (ρ : Representation A G V)

/-- The **`σ`-twist** `ρ^σ` of a representation by a ring automorphism `σ` of `A`: the same
operators, on the `σ`-twist of `V`. -/
def coeffTwist : Representation A G (CoeffTwist σ V) where
  toFun g :=
    { toFun x := CoeffTwist.of σ V (ρ g ((CoeffTwist.of σ V).symm x))
      map_add' x y := by simp
      map_smul' a x := by
        induction x using CoeffTwist.induction
        simp [CoeffTwist.smul_of] }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

variable {σ ρ}

@[simp]
theorem coeffTwist_apply_of (g : G) (v : V) :
    ρ.coeffTwist σ g (CoeffTwist.of σ V v) = CoeffTwist.of σ V (ρ g v) :=
  (rfl)

/-- `ρ^σ(g)` sends `v` to `w` exactly when `ρ(g)` does. -/
theorem coeffTwist_apply_eq_iff (g : G) (v w : V) :
    ρ.coeffTwist σ g (CoeffTwist.of σ V v) = CoeffTwist.of σ V w ↔ ρ g v = w := by
  simp

/-- **Twisting keeps stabilizers.** -/
@[simp]
theorem stabilizer_coeffTwist (v : V) :
    (ρ.coeffTwist σ).stabilizer (CoeffTwist.of σ V v) = ρ.stabilizer v := by
  ext g
  simp [mem_stabilizer]

variable (σ ρ) in
/-- The `σ`-twist of a restriction is the restriction of the `σ`-twist. -/
theorem coeffTwist_comp {H : Type*} [Group H] (f : H →* G) :
    (ρ.coeffTwist σ).comp f = Representation.coeffTwist σ (ρ.comp f) :=
  (rfl)

/-- `CoeffTwist.of σ V v` is invariant under `ρ^σ` exactly when `v` is invariant under `ρ`. -/
theorem of_mem_invariants_coeffTwist (v : V) :
    CoeffTwist.of σ V v ∈ invariants (ρ.coeffTwist σ) ↔ v ∈ invariants ρ := by
  simp only [mem_invariants]
  exact forall_congr' fun g ↦ coeffTwist_apply_eq_iff g v v

section Topology

variable [TopologicalSpace G]

/-- **Twisting preserves smoothness**, in both directions. -/
theorem isSmooth_coeffTwist_iff : IsSmooth (ρ.coeffTwist σ) ↔ IsSmooth ρ :=
  ⟨fun h ↦ ⟨fun v ↦ by simpa using h.isOpen_stabilizer (CoeffTwist.of σ V v)⟩,
    fun h ↦ ⟨fun x ↦ by
      induction x using CoeffTwist.induction
      rw [stabilizer_coeffTwist]
      exact h.isOpen_stabilizer _⟩⟩

instance [IsSmooth ρ] : IsSmooth (ρ.coeffTwist σ) :=
  isSmooth_coeffTwist_iff.2 ‹_›

variable (σ ρ) in
/-- The `σ`-semilinear map `V^U → (V^σ)^U` between the invariants of a subgroup `U` in `ρ` and in
its `σ`-twist, the identity on vectors. -/
def invariantsToCoeffTwist (U : Subgroup G) :
    invariants (ρ.comp U.subtype) →ₛₗ[(σ : A →+* A)]
      invariants ((ρ.coeffTwist σ).comp U.subtype) where
  toFun v := ⟨CoeffTwist.of σ V v, by
    rw [coeffTwist_comp]
    exact (of_mem_invariants_coeffTwist (ρ := ρ.comp U.subtype) v).2 v.property⟩
  map_add' _ _ := rfl
  map_smul' a v := Subtype.ext (CoeffTwist.of_smul a v.val)

omit [TopologicalSpace G] in
theorem invariantsToCoeffTwist_surjective (U : Subgroup G) :
    Function.Surjective (invariantsToCoeffTwist σ ρ U) := by
  rintro ⟨x, hx⟩
  induction x using CoeffTwist.induction with | h v => ?_
  rw [coeffTwist_comp, of_mem_invariants_coeffTwist] at hx
  exact ⟨⟨v, hx⟩, rfl⟩

variable (σ ρ) in
/-- The `σ⁻¹`-semilinear map `(V^σ)^U → V^U`, the identity on vectors. -/
def invariantsOfCoeffTwist (U : Subgroup G) :
    invariants ((ρ.coeffTwist σ).comp U.subtype) →ₛₗ[(σ.symm : A →+* A)]
      invariants (ρ.comp U.subtype) where
  toFun x := ⟨(CoeffTwist.of σ V).symm x, by
    obtain ⟨x, hx⟩ := x
    induction x using CoeffTwist.induction with | h v => ?_
    rw [coeffTwist_comp, of_mem_invariants_coeffTwist] at hx
    exact hx⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [TopologicalSpace G] in
theorem invariantsOfCoeffTwist_surjective (U : Subgroup G) :
    Function.Surjective (invariantsOfCoeffTwist σ ρ U) :=
  fun v ↦ ⟨invariantsToCoeffTwist σ ρ U v, rfl⟩

/-- **Twisting preserves admissibility**, in both directions: the invariants of a compact open
subgroup are carried to each other by a `σ`-semilinear bijection. -/
theorem isAdmissible_coeffTwist_iff : IsAdmissible (ρ.coeffTwist σ) ↔ IsAdmissible ρ := by
  simp only [isAdmissible_iff, isSmooth_coeffTwist_iff]
  refine and_congr_right fun _ ↦ forall₂_congr fun U _ ↦ ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · exact Module.Finite.of_surjective _ (invariantsOfCoeffTwist_surjective (σ := σ) (ρ := ρ) U)
  · exact Module.Finite.of_surjective _ (invariantsToCoeffTwist_surjective (σ := σ) (ρ := ρ) U)

instance [IsAdmissible ρ] : IsAdmissible (ρ.coeffTwist σ) :=
  isAdmissible_coeffTwist_iff.2 ‹_›

end Topology

variable (σ ρ) in
/-- **The subrepresentations of `ρ` and `ρ^σ` are the same subsets of `V`**: a subset is stable
under `ρ` and closed under the action of `A` exactly when it is stable under `ρ^σ` and closed under
the twisted action, because `σ` is bijective. -/
def subrepresentationCoeffTwistOrderIso :
    Subrepresentation ρ ≃o Subrepresentation (ρ.coeffTwist σ) where
  toFun W :=
    { toSubmodule :=
        { carrier := (CoeffTwist.of σ V).symm ⁻¹' W.toSubmodule
          add_mem' := W.toSubmodule.add_mem
          zero_mem' := W.toSubmodule.zero_mem
          smul_mem' a _ hx := W.toSubmodule.smul_mem (σ.symm a) hx }
      apply_mem_toSubmodule g _ hx := W.apply_mem_toSubmodule g hx }
  invFun W :=
    { toSubmodule :=
        { carrier := CoeffTwist.of σ V ⁻¹' W.toSubmodule
          add_mem' := W.toSubmodule.add_mem
          zero_mem' := W.toSubmodule.zero_mem
          smul_mem' a v hv := by
            rw [Set.mem_preimage, CoeffTwist.of_smul]
            exact W.toSubmodule.smul_mem (σ a) hv }
      apply_mem_toSubmodule g _ hv := W.apply_mem_toSubmodule g hv }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- **Twisting preserves irreducibility**, in both directions, over a field. -/
theorem isIrreducible_coeffTwist_iff {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {σ : k ≃+* k} {ρ : Representation k G V} : IsIrreducible (ρ.coeffTwist σ) ↔ IsIrreducible ρ :=
  (subrepresentationCoeffTwistOrderIso σ ρ).isSimpleOrder_iff.symm

end Representation

namespace TauCeti

namespace SmoothRep

open Representation

variable {A : Type u} [CommRing A] {G : Type v} [Group G]

/-- The intertwining map `ρ^σ → ρ'^σ` with the same underlying function as `f : ρ → ρ'`. -/
def _root_.Representation.IntertwiningMap.coeffTwist {V W : Type*} [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W] {ρ : Representation A G V} {ρ' : Representation A G W}
    (σ : A ≃+* A) (f : ρ.IntertwiningMap ρ') :
    (ρ.coeffTwist σ).IntertwiningMap (ρ'.coeffTwist σ) where
  toFun x := CoeffTwist.of σ W (f ((CoeffTwist.of σ V).symm x))
  map_add' x y := by simp
  map_smul' a x := by
    induction x using CoeffTwist.induction
    simp [CoeffTwist.smul_of]
  isIntertwining' g := by
    ext x
    induction x using CoeffTwist.induction
    simp [IntertwiningMap.isIntertwining]

@[simp]
theorem _root_.Representation.IntertwiningMap.coeffTwist_apply_of {V W : Type*} [AddCommGroup V]
    [Module A V] [AddCommGroup W] [Module A W] {ρ : Representation A G V}
    {ρ' : Representation A G W} (σ : A ≃+* A) (f : ρ.IntertwiningMap ρ') (v : V) :
    f.coeffTwist σ (CoeffTwist.of σ V v) = CoeffTwist.of σ W (f v) :=
  (rfl)

variable [TopologicalSpace G] (σ : A ≃+* A)

/-- **The `σ`-twist functor** `SmoothRep A G ⥤ SmoothRep A G`, `V ↦ V^σ`, acting on morphisms by
the same underlying maps. -/
abbrev coeffTwist : SmoothRep.{w} A G ⥤ SmoothRep.{w} A G where
  obj V := SmoothRep.of (V.obj.ρ.coeffTwist σ)
  map f := ObjectProperty.homMk (Rep.ofHom (f.hom.hom.coeffTwist σ))

/-- The isomorphism of smooth representations given by a linear equivalence of the underlying
modules that intertwines the actions. -/
def coeffTwistIsoOfEq {V W : SmoothRep.{w} A G}
    (e : V.obj.V ≃ₗ[A] W.obj.V) (he : ∀ g, e ∘ₗ V.obj.ρ g = W.obj.ρ g ∘ₗ e) : V ≅ W :=
  ObjectProperty.isoMk _ (Rep.mkIso
    { toLinearEquiv := e
      isIntertwining' g := he g })

/-- **Twisting by the identity is the identity functor.** -/
def coeffTwistReflIso : coeffTwist.{w} (RingEquiv.refl A) ≅ 𝟭 (SmoothRep.{w} A G) :=
  NatIso.ofComponents
    (fun V ↦ coeffTwistIsoOfEq
      { toFun := (CoeffTwist.of (RingEquiv.refl A) V.obj.V).symm
        invFun := CoeffTwist.of (RingEquiv.refl A) V.obj.V
        map_add' _ _ := rfl
        map_smul' _ _ := rfl
        left_inv _ := rfl
        right_inv _ := rfl }
      fun _ ↦ rfl)
    fun _ ↦ rfl

/-- **Twisting by `σ` and then by `τ` is twisting by `σ.trans τ = τ ∘ σ`.** -/
def coeffTwistTransIso (τ : A ≃+* A) :
    coeffTwist.{w} σ ⋙ coeffTwist τ ≅ coeffTwist.{w, u, v} (G := G) (σ.trans τ) :=
  NatIso.ofComponents
    (fun V ↦ coeffTwistIsoOfEq
      { toFun x := CoeffTwist.of (σ.trans τ) V.obj.V ((CoeffTwist.of σ V.obj.V).symm
          ((CoeffTwist.of τ (CoeffTwist σ V.obj.V)).symm x))
        invFun x := CoeffTwist.of τ (CoeffTwist σ V.obj.V) (CoeffTwist.of σ V.obj.V
          ((CoeffTwist.of (σ.trans τ) V.obj.V).symm x))
        map_add' _ _ := rfl
        map_smul' _ _ := rfl
        left_inv _ := rfl
        right_inv _ := rfl }
      fun _ ↦ rfl)
    fun _ ↦ rfl

/-- **The `σ`-twist is an autoequivalence** of `SmoothRep A G`, with inverse the twist by `σ⁻¹`. -/
def coeffTwistEquiv : SmoothRep.{w} A G ≌ SmoothRep.{w} A G where
  functor := coeffTwist σ
  inverse := coeffTwist σ.symm
  unitIso := NatIso.ofComponents
    (fun V ↦ coeffTwistIsoOfEq
      { toFun v := CoeffTwist.of σ.symm (CoeffTwist σ V.obj.V) (CoeffTwist.of σ V.obj.V v)
        invFun x := (CoeffTwist.of σ V.obj.V).symm
          ((CoeffTwist.of σ.symm (CoeffTwist σ V.obj.V)).symm x)
        map_add' _ _ := rfl
        map_smul' a v := by
          rw [RingHom.id_apply, CoeffTwist.smul_of, CoeffTwist.smul_of, RingEquiv.symm_symm,
            RingEquiv.symm_apply_apply]
        left_inv _ := rfl
        right_inv _ := rfl }
      fun _ ↦ rfl)
    fun _ ↦ rfl
  counitIso := NatIso.ofComponents
    (fun V ↦ coeffTwistIsoOfEq
      { toFun x := (CoeffTwist.of σ.symm V.obj.V).symm
          ((CoeffTwist.of σ (CoeffTwist σ.symm V.obj.V)).symm x)
        invFun v := CoeffTwist.of σ (CoeffTwist σ.symm V.obj.V) (CoeffTwist.of σ.symm V.obj.V v)
        map_add' _ _ := rfl
        map_smul' a x := by
          change σ.symm.symm (σ.symm a) • ((CoeffTwist.of σ.symm V.obj.V).symm
            ((CoeffTwist.of σ (CoeffTwist σ.symm V.obj.V)).symm x)) = a • _
          rw [RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
        left_inv _ := rfl
        right_inv _ := rfl }
      fun _ ↦ rfl)
    fun _ ↦ rfl
  functor_unitIso_comp _ := rfl

instance isEquivalence_coeffTwist : (coeffTwist.{w} (G := G) σ).IsEquivalence :=
  inferInstanceAs (coeffTwistEquiv.{w} (G := G) σ).functor.IsEquivalence

end SmoothRep

end TauCeti

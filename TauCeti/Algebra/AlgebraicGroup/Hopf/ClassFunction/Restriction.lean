/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.WeylGroup
public import TauCeti.Algebra.AlgebraicGroup.Hopf.ClassFunction.Basic

/-!
# Restriction of class functions to a diagonalizable subgroup

Let `G = Spec H` be an affine group scheme over a commutative ring `R` with connected prime
spectrum, and let `D(X) → G` be a closed diagonalizable subgroup, given by a surjective morphism
`π : H →ₐc[R] R[X]` of coordinate Hopf algebras. Restriction of functions along `D(X) → G` is the
algebra map `π`. This file shows that it sends every regular class function of `G` to a function
on `D(X)` fixed by the Weyl group `BialgHom.weylGroup π hπ`, acting on `R[X]` through its
action on the character group `X`. So restriction is an algebra map from the class functions
`C(G)` to the Weyl-invariant functions `R[X]^W` on `D(X)`; geometrically, it is the morphism
`D(X)/W → Conj(G)` of quotients induced by the inclusion. When `D(X)` is a split maximal torus `T`
of a connected reductive group `G` over a field, Chevalley's restriction theorem for groups
asserts that this map `C(G) → O(T)^W` is an isomorphism, so that `Conj(G) ≅ T/W`; that theorem
is not proved here.

The invariance comes from two facts. Conjugation by a rational point fixes every class function
(`TauCeti.HopfAlgebra.pointConjugationAlgHom_apply_of_mem_classFunctions`). An element `w` of the
Weyl group is realized by a rational point `g` normalizing `D(X)`, whose inverse conjugation
restricts to `D(X)` as the automorphism of `R[X]` induced by `w`. Only rational normalizing points
enter, as in the definition of `BialgHom.weylGroup`.

## Main declarations

* `TauCeti.HopfAlgebra.pointConjugationAlgHom_apply_of_mem_classFunctions`: conjugation by a
  rational point fixes class functions.
* `BialgHom.weylInvariants`: the subalgebra of functions on `D(X)` fixed by the Weyl
  group, with `BialgHom.mem_weylInvariants_iff`.
* `BialgHom.weylInvariants_eq_top_of_isCocomm`: on a commutative group, such as `𝔾ₘ`, every
  function on `D(X)` is Weyl invariant.
* `BialgHom.map_mem_weylInvariants`: the restriction of a class function to `D(X)` is Weyl
  invariant.
* `BialgHom.classFunctionsRestrict`: restriction as an algebra map from the class functions to
  the Weyl invariants.

## References

* R. Steinberg, *Regular elements of semisimple algebraic groups*, Publ. Math. IHÉS 25 (1965),
  §6, Lemma 6.2 and Corollary 6.4.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 21.
-/

public section

open TensorProduct

namespace TauCeti.HopfAlgebra

variable {R H : Type*} [CommSemiring R] [CommSemiring H] [_root_.HopfAlgebra R H]

/-- **Conjugation by a rational point fixes every class function.** -/
theorem pointConjugationAlgHom_apply_of_mem_classFunctions {f : H}
    (hf : f ∈ classFunctions R H) (g : WithConv (H →ₐ[R] R)) :
    pointConjugationAlgHom g f = f := by
  simpa [mem_classFunctions_iff.mp hf] using LinearMap.apply_pointConjugationAlgHom LinearMap.id g f

end TauCeti.HopfAlgebra

namespace BialgHom

open TauCeti TauCeti.HopfAlgebra

variable {R H X : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
  [ConnectedSpace (PrimeSpectrum R)]
variable (π : H →ₐc[R] MonoidAlgebra R X) (hπ : Function.Surjective π)

/-- The **Weyl-invariant functions** on the closed diagonalizable subgroup `D(X) → G`: the functions
in `R[X]` fixed by every element of the Weyl group `BialgHom.weylGroup π hπ`, acting
through its action on the character group `X`. It is the coordinate algebra `O(D(X))^W` of the
quotient of `D(X)` by the Weyl group. -/
noncomputable def weylInvariants : Subalgebra R (MonoidAlgebra R X) :=
  ⨅ w : weylGroup π hπ,
    AlgHom.equalizer (MonoidAlgebra.domCongr R R (w : MulAut X)).toAlgHom (AlgHom.id R _)

variable {π hπ} in
/-- A function on `D(X)` is Weyl invariant exactly when every element of the Weyl group fixes
it. -/
@[simp]
theorem mem_weylInvariants_iff {p : MonoidAlgebra R X} :
    p ∈ weylInvariants π hπ ↔ ∀ w ∈ weylGroup π hπ, MonoidAlgebra.domCongr R R w p = p := by
  simp [weylInvariants, Algebra.mem_iInf, AlgHom.mem_equalizer]

/-- On a commutative group scheme every function on a closed diagonalizable subgroup is Weyl
invariant; for instance `O(𝔾ₘ)^W` is the whole Laurent polynomial ring `R[t, t⁻¹]`. -/
@[simp]
theorem weylInvariants_eq_top_of_isCocomm [Coalgebra.IsCocomm R H] : weylInvariants π hπ = ⊤ :=
  eq_top_iff.mpr fun p _ ↦ mem_weylInvariants_iff.mpr fun w hw ↦ by
    rw [weylGroup_eq_bot_of_isCocomm, Subgroup.mem_bot] at hw
    simp [hw, MulAut.one_def]

/-- **Class functions restrict to Weyl-invariant functions.** The restriction to the closed
diagonalizable subgroup `D(X)` of a regular class function of `G` is fixed by the Weyl group. -/
theorem map_mem_weylInvariants {f : H} (hf : f ∈ classFunctions R H) :
    π f ∈ weylInvariants π hπ := by
  refine mem_weylInvariants_iff.mpr fun w hw ↦ ?_
  obtain ⟨g, hg⟩ := (mem_weylGroup_iff π hπ).mp hw
  simpa [pointConjugationAlgHom_apply_of_mem_classFunctions hf] using (AlgHom.congr_fun hg f).symm

/-- **The Chevalley restriction map**: restriction of functions along the closed diagonalizable
subgroup `D(X) → G`, as an algebra map from the class functions of `G` to the Weyl-invariant
functions on `D(X)`. Geometrically it is the morphism `D(X)/W → Conj(G)` induced by the inclusion;
for a split maximal torus of a connected reductive group over a field, Chevalley's restriction
theorem says it is an isomorphism. -/
noncomputable def classFunctionsRestrict : classFunctions R H →ₐ[R] weylInvariants π hπ :=
  ((π : H →ₐ[R] MonoidAlgebra R X).comp (classFunctions R H).val).codRestrict _
    fun f ↦ map_mem_weylInvariants π hπ f.property

@[simp]
theorem coe_classFunctionsRestrict (f : classFunctions R H) :
    (classFunctionsRestrict π hπ f : MonoidAlgebra R X) = π f :=
  (rfl)

/-- The Chevalley restriction map is the restriction of `π` to the class functions. -/
theorem val_comp_classFunctionsRestrict :
    (weylInvariants π hπ).val.comp (classFunctionsRestrict π hπ) =
      (π : H →ₐ[R] MonoidAlgebra R X).comp (classFunctions R H).val :=
  AlgHom.ext fun _ ↦ coe_classFunctionsRestrict π hπ _

end BialgHom

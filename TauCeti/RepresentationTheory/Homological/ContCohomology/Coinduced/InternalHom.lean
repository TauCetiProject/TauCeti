/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.Equiv
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Pairing
public import TauCeti.Topology.Algebra.GroupAction.InternalHom.Basic

/-!
# The internal hom out of a coinduced module

Let `U` be a subgroup of finite index of a topological group `G`, let `A` be a `U`-module and `N`
a `G`-module. The additive homomorphisms out of the coinduced module `Coind_U^G A`, carrying the
conjugation action of `G` of `TauCeti.InternalHom`, receive a `G`-equivariant homomorphism from a
coinduced module:

```text
Coind_U^G Hom(A, N) → Hom(Coind_U^G A, N),    F ↦ (f ↦ tr (g ↦ F g (f g))),
```

the trace along `G ⧸ U` of the pointwise evaluation pairing (`TauCeti.DiscreteCoind.toInternalHom`).
For an open `U` and a discrete `U`-module `A` it is injective, and it is bijective as soon as
moreover the conjugation action of `U` on `Hom(A, N)` is continuous
(`TauCeti.DiscreteCoind.toInternalHomEquiv`), which is the case for a finite `A` and a discrete
`G`-module `N`. This is the finite-index coincidence of induction and coinduction read on the dual:
for finite index, `Hom(Ind_U^G A, N) ≅ Coind_U^G Hom(A, N)`.

On the single `single g a`, the coinduced function supported on the right coset `U * g` with
value `a` at `g`, the image of `F` evaluates to `g⁻¹ • F g a` (`toInternalHom_single`). Since the
singles span `Coind_U^G A` this gives injectivity. The preimage of `φ : Coind_U^G A →+ N` is
`g ↦ (a ↦ g • φ (single g a))` (`toInternalHomEquiv_symm_apply`), which is `U`-equivariant, hence
locally constant when the conjugation action of `U` on `Hom(A, N)` is continuous; for a finite
discrete `A` and a discrete `N` this continuity is the `ContinuousSMul` instance of
`TauCeti.InternalHom`.

For the permutation module `Coind_U^G 𝔽_p` of an open subgroup `U` of a pro-`p` group this says
that `Hom(Coind_U^G 𝔽_p, 𝔽_p) ≅ Coind_U^G 𝔽_p`: the permutation module is self-dual, so its
`G`-invariant functionals are, through Shapiro's isomorphism in degree zero, the `U`-invariants of
`𝔽_p`, a line. That identifies the source of the target of Tate's duality map
`H²(G, M) → Hom(H⁰(G, Hom(M, 𝔽_p)), H²(G, 𝔽_p))` at `M = Coind_U^G 𝔽_p`, which is how the second
cohomology of an open subgroup of a Demushkin group is computed through the duality of the ambient
group (Serre, *Structure de certains pro-p-groupes*, §9.2).

## Main definitions

* `TauCeti.DiscreteCoind.toInternalHom`: the `G`-equivariant homomorphism
  `Coind_U^G Hom(A, N) →+[G] Hom(Coind_U^G A, N)`, trace of the pointwise evaluation pairing, for
  a subgroup `U` of finite index.
* `TauCeti.DiscreteCoind.toInternalHomEquiv`: the additive equivalence
  `Coind_U^G Hom(A, N) ≃+ Hom(Coind_U^G A, N)` it induces for an open `U`, a discrete `U`-module
  `A` and a continuous conjugation action of `U` on `Hom(A, N)`.

## Main results

* `TauCeti.DiscreteCoind.toAddMonoidHom_toInternalHom_apply` and
  `TauCeti.DiscreteCoind.toInternalHom_apply_eq_sum`: the value of `toInternalHom F` at `f`
  is the trace of `g ↦ F g (f g)`, that is `∑_{x : G ⧸ U} x.out • F x.out⁻¹ (f x.out⁻¹)`.
* `TauCeti.DiscreteCoind.toInternalHom_single`: `toInternalHom F (single g a) = g⁻¹ • F g a`, for
  an open `U` and a discrete `U`-module `A`.
* `TauCeti.DiscreteCoind.toInternalHom_injective`: `toInternalHom` is injective for an open `U` and
  a discrete `U`-module `A`.
* `TauCeti.DiscreteCoind.toInternalHom_surjective` and
  `TauCeti.DiscreteCoind.toInternalHom_bijective`: `toInternalHom` is bijective for an open `U` and
  a discrete `U`-module `A` whenever the conjugation action of `U` on `Hom(A, N)` is continuous, in
  particular for a finite `A` and a discrete `G`-module `N`.
* `TauCeti.DiscreteCoind.toInternalHomEquiv_symm_apply`: the inverse of `toInternalHomEquiv` sends
  `φ` to `g ↦ (a ↦ g • φ (single g a))`.
* `TauCeti.DiscreteCoind.toInternalHomEquiv_smul` and
  `TauCeti.DiscreteCoind.toInternalHomEquiv_symm_smul`: both directions of `toInternalHomEquiv`
  are `G`-equivariant.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter III, §5: induced and
  coinduced modules along a subgroup of finite index.
* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.2.
-/

public section

namespace TauCeti.DiscreteCoind

universe u v w

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Trace

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G] (U : Subgroup G)
  [U.FiniteIndex] (A : Type v) [AddCommGroup A] [DistribMulAction U A]
  (N : Type w) [AddCommGroup N] [DistribMulAction G N]

/-- **The internal hom out of a coinduced module.** For a subgroup `U` of finite index, a
coinduced homomorphism `F : Coind_U^G Hom(A, N)` defines the homomorphism
`f ↦ tr (g ↦ F g (f g))` on `Coind_U^G A`, the trace along `G ⧸ U` of the pointwise evaluation
pairing. The assignment is `G`-equivariant for the conjugation action on the internal hom. For an
open `U` and a discrete `U`-module `A` it is injective (`toInternalHom_injective`), and it is a
bijection when moreover the conjugation action of `U` on `Hom(A, N)` is continuous
(`toInternalHom_bijective`), as it is for a finite `A` and a discrete `N`. -/
noncomputable def toInternalHom :
    DiscreteCoind G U (InternalHom U A N) →+[G] InternalHom G (DiscreteCoind G U A) N where
  toFun F := InternalHom.of G ((trace G U N : DiscreteCoind G U N →+ N).comp
    (pointwisePairing U (InternalHom.evalPairing U) (InternalHom.evalPairing_equivariant (G := U))
      F))
  map_zero' := by rw [map_zero, AddMonoidHom.comp_zero, InternalHom.of_zero]
  map_add' F F' := by rw [map_add, AddMonoidHom.comp_add, InternalHom.of_add]
  map_smul' g F := InternalHom.ext <| AddMonoidHom.ext fun f => by
    rw [InternalHom.toAddMonoidHom_smul, homAction_apply]
    simp only [AddMonoidHom.comp_apply, DistribMulActionHom.coe_fn_coe, MonoidHom.id_apply]
    conv_lhs => rw [← smul_inv_smul g f]
    rw [pointwisePairing_smul, _root_.map_smul]

/-- The value of `toInternalHom F` at `f` is the trace of the pointwise evaluation pairing
`g ↦ F g (f g)`. -/
@[simp]
theorem toAddMonoidHom_toInternalHom_apply (F : DiscreteCoind G U (InternalHom U A N))
    (f : DiscreteCoind G U A) :
    (toInternalHom U A N F).toAddMonoidHom f =
      trace G U N (pointwisePairing U (InternalHom.evalPairing U)
        (InternalHom.evalPairing_equivariant (G := U)) F f) := (rfl)

/-- The value of `toInternalHom F` at `f`, as a sum over the cosets:
`∑_{x : G ⧸ U} x.out • F x.out⁻¹ (f x.out⁻¹)`. -/
theorem toInternalHom_apply_eq_sum (F : DiscreteCoind G U (InternalHom U A N))
    (f : DiscreteCoind G U A) :
    (toInternalHom U A N F).toAddMonoidHom f =
      ∑ x : G ⧸ U, x.out • (F x.out⁻¹).toAddMonoidHom (f x.out⁻¹) := by
  rw [toAddMonoidHom_toInternalHom_apply, trace_apply]
  simp only [pointwisePairing_apply, InternalHom.evalPairing_apply]

section Open

variable [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul U A] (hU : IsOpen (U : Set G))

/-- **`toInternalHom` on a single**: `toInternalHom F (single g a) = g⁻¹ • F g a`. The pointwise
pairing `g' ↦ F g' (single g a g')` is supported on the right coset `U * g`, so only that coset
contributes to the trace. Not a `simp` lemma, because
`TauCeti.DiscreteCoind.toAddMonoidHom_toInternalHom_apply` already takes its left-hand side
apart. -/
theorem toInternalHom_single (F : DiscreteCoind G U (InternalHom U A N)) (g : G) (a : A) :
    (toInternalHom U A N F).toAddMonoidHom (single G U A hU g a) =
      g⁻¹ • (F g).toAddMonoidHom a := by
  rw [toAddMonoidHom_toInternalHom_apply, trace_eq_inv_smul_apply _ g, pointwisePairing_apply,
    single_apply_self, InternalHom.evalPairing_apply]
  intro x hx
  rw [pointwisePairing_apply, single_apply_of_notMem hU a hx, map_zero]

include hU in
/-- `toInternalHom` is injective for an open subgroup `U` and a discrete `U`-module `A`: a
coinduced homomorphism is recovered from its image by evaluating on singles. -/
theorem toInternalHom_injective : Function.Injective (toInternalHom U A N) := fun F F' h => by
  refine DiscreteCoind.ext fun g => InternalHom.ext (AddMonoidHom.ext fun a => ?_)
  have h' := congrArg
    (fun φ : InternalHom G (DiscreteCoind G U A) N => φ.toAddMonoidHom (single G U A hU g a)) h
  simp only [toInternalHom_single] at h'
  exact MulAction.injective g⁻¹ h'

end Open

end Trace

section Surjective

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G] (U : Subgroup G)
  [U.FiniteIndex] (A : Type v) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A] [ContinuousSMul U A]
  (N : Type w) [AddCommGroup N] [DistribMulAction G N] [ContinuousSMul U (InternalHom U A N)]
  (hU : IsOpen (U : Set G))

include hU in
/-- `toInternalHom` is surjective for an open subgroup `U` and a discrete `U`-module `A` whose
internal hom `Hom(A, N)` carries a continuous conjugation action of `U`, as it does for a finite `A`
and a discrete `N`: a homomorphism `φ : Coind_U^G A →+ N` is the image of
`g ↦ (a ↦ g • φ (single g a))`, which is `U`-equivariant by `single_mul`, hence locally constant
by the continuity of the action on `Hom(A, N)`, and which `toInternalHom` sends back to `φ` by the
decomposition of a coinduced function into its singles. -/
theorem toInternalHom_surjective : Function.Surjective (toInternalHom U A N) := fun φ => by
  let k : G → InternalHom U A N := fun g => InternalHom.of U
    ((DistribSMul.toAddMonoidHom N g).comp (φ.toAddMonoidHom.comp (single G U A hU g)))
  have hk : ∀ (u : U) (g : G), k ((u : G) * g) = u • k g := fun u g =>
    InternalHom.ext <| AddMonoidHom.ext fun a => by
      simp only [k, InternalHom.toAddMonoidHom_smul, homAction_apply, AddMonoidHom.comp_apply,
        DistribSMul.toAddMonoidHom_apply, single_mul, Subgroup.smul_def, mul_smul]
  refine ⟨mk G U _ k (isLocallyConstant_of_apply_mul hU hk) hk,
    InternalHom.ext (AddMonoidHom.ext fun f => ?_)⟩
  rw [toInternalHom_apply_eq_sum]
  conv_rhs => rw [← sum_single hU f, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [k, mk_apply, AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply,
    smul_inv_smul]

include hU in
/-- **The internal hom out of a coinduced module is coinduced**: for an open subgroup `U` of
finite index and a discrete `U`-module `A` whose internal hom `Hom(A, N)` carries a continuous
conjugation action of `U`, in particular for a finite `A` and a discrete `N`, `toInternalHom` is a
`G`-equivariant bijection `Coind_U^G Hom(A, N) ≅ Hom(Coind_U^G A, N)`. -/
theorem toInternalHom_bijective : Function.Bijective (toInternalHom U A N) :=
  ⟨toInternalHom_injective U A N hU, toInternalHom_surjective U A N hU⟩

/-- **The internal hom out of a coinduced module is coinduced**, as an additive equivalence
`Coind_U^G Hom(A, N) ≃+ Hom(Coind_U^G A, N)`: `toInternalHom` bundled with its inverse, under the
hypotheses of `toInternalHom_bijective`. Its forward map is `toInternalHom`
(`toInternalHomEquiv_apply`), its inverse sends `φ` to `g ↦ (a ↦ g • φ (single g a))`
(`toInternalHomEquiv_symm_apply`), and both directions are `G`-equivariant
(`toInternalHomEquiv_smul`, `toInternalHomEquiv_symm_smul`). -/
noncomputable def toInternalHomEquiv :
    DiscreteCoind G U (InternalHom U A N) ≃+ InternalHom G (DiscreteCoind G U A) N :=
  AddEquiv.ofBijective (toInternalHom U A N) (toInternalHom_bijective U A N hU)

/-- `toInternalHomEquiv` is `toInternalHom` on elements. -/
@[simp]
theorem toInternalHomEquiv_apply (F : DiscreteCoind G U (InternalHom U A N)) :
    toInternalHomEquiv U A N hU F = toInternalHom U A N F := (rfl)

/-- The inverse of `toInternalHomEquiv` sends `φ : Coind_U^G A →+ N` to the coinduced homomorphism
`g ↦ (a ↦ g • φ (single g a))`: evaluating `φ` on the single `single g a` recovers `g⁻¹ • F g a`
(`toInternalHom_single`), so `g • φ (single g a) = F g a`. -/
@[simp]
theorem toInternalHomEquiv_symm_apply (φ : InternalHom G (DiscreteCoind G U A) N) (g : G) (a : A) :
    ((toInternalHomEquiv U A N hU).symm φ g).toAddMonoidHom a =
      g • φ.toAddMonoidHom (single G U A hU g a) := by
  conv_rhs => rw [← (toInternalHomEquiv U A N hU).apply_symm_apply φ, toInternalHomEquiv_apply,
    toInternalHom_single, smul_inv_smul]

/-- `toInternalHomEquiv` is `G`-equivariant. -/
theorem toInternalHomEquiv_smul (g : G) (F : DiscreteCoind G U (InternalHom U A N)) :
    toInternalHomEquiv U A N hU (g • F) = g • toInternalHomEquiv U A N hU F := by
  rw [toInternalHomEquiv_apply, toInternalHomEquiv_apply, _root_.map_smul]

/-- The inverse of `toInternalHomEquiv` is `G`-equivariant. -/
theorem toInternalHomEquiv_symm_smul (g : G) (φ : InternalHom G (DiscreteCoind G U A) N) :
    (toInternalHomEquiv U A N hU).symm (g • φ) = g • (toInternalHomEquiv U A N hU).symm φ :=
  AddEquiv.symm_map_smul_of_map_smul _ (toInternalHomEquiv_smul U A N hU) g φ

end Surjective

end TauCeti.DiscreteCoind

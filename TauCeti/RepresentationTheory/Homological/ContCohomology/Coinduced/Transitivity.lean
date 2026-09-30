/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# Transitivity of discrete coinduction

Let `G` be a topological group, `U ≤ G` a subgroup with compact closure and `V ≤ U` a subgroup of
`U`. For a discrete `V`-module `A`, coinducing first to `U` and then to `G` is the same as
coinducing to `G` in one step:

```text
Coind_U^G (Coind_V^U A) ≅ Coind_V^G A,   f ↦ (g ↦ f g 1),
```

with inverse `φ ↦ (g ↦ (u ↦ φ (u * g)))`. This is the coinduced form of the transitivity
`Ind_V^G = Ind_U^G ∘ Ind_V^U` of induction, and it is the identification of coefficient modules that
the dimension-shifting proof of Shapiro's lemma in every degree runs on: the acyclic module
`Coind_1^G A` of the trivial subgroup of `G` is the coinduction from `U` of the acyclic module
`Coind_1^U A` of the trivial subgroup of `U`.

Since `TauCeti.DiscreteCoind` coinduces from a subgroup of the ambient group, the inner subgroup is
a subgroup `V` of the subtype `U`, and the one-step coinduction is from the subgroup `W` of `G`
with the same elements, that is `W = V.map U.subtype`. The module `A` then carries an action of `V`
and an action of `W`, and the statement requires them to agree on elements with the same underlying
element of `G`; both hypotheses are explicit arguments rather than a definitional identification
of the two subgroups, whose types differ. The case used by dimension shifting is `V = ⊥` and
`W = ⊥`, where every action of the trivial group is trivial and the agreement is automatic.

The topological input is that `U` is relatively compact in `G`, `IsCompact (closure U)`: a locally
constant function on `G` is then locally constant under right translation uniformly in the
translating element `u ∈ U` (`TauCeti.exists_isOpen_forall_mem_mul_right_eq`), which is what makes
`g ↦ (u ↦ φ (u * g))` locally constant. In a compact group, as in the profinite setting, every
subgroup is relatively compact.

## Main definitions

* `TauCeti.DiscreteCoind.transEquiv`: the additive equivalence
  `Coind_U^G (Coind_V^U A) ≃+ Coind_W^G A`, which is `G`-equivariant
  (`TauCeti.DiscreteCoind.transEquiv_smul`) and compatible with evaluation at `1`
  (`TauCeti.DiscreteCoind.eval_transEquiv`).
* `TauCeti.DiscreteCoind.transIso`: the same identification as an isomorphism of the topological
  `G`-representations attached to the two discrete modules by `TauCeti.ofDiscreteModule`.
* `TauCeti.DiscreteCoind.transIsoBot`: its case `V = W = ⊥`,
  `Coind_U^G (Coind_1^U A) ≅ Coind_1^G A`, the identification dimension shifting uses.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Ch. I §6, where the coinduced module is written `Ind` (see the footnote on p. 61).
* L. Ribes, P. Zalesskii, *Profinite Groups*, Section 6.10.
-/

public section

namespace TauCeti.DiscreteCoind

section Transitivity

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} {V : Subgroup U} {W : Subgroup G}
  {A : Type*} [AddCommGroup A] [DistribMulAction V A] [DistribMulAction W A]
  (hW : V.map U.subtype = W)
  (hsmul : ∀ (v : V) (w : W) (a : A), ((v : U) : G) = (w : G) → w • a = v • a)
  (hU : IsCompact (closure (U : Set G)))

/-- **Transitivity of discrete coinduction**: `Coind_U^G (Coind_V^U A) ≃+ Coind_W^G A` for
`V ≤ U ≤ G` with `U` relatively compact in `G`, where `W` is `V` regarded as a subgroup of `G`.
The forward map evaluates the inner coinduced function at `1`, `f ↦ (g ↦ f g 1)`; the inverse is
`φ ↦ (g ↦ (u ↦ φ (u * g)))`. -/
def transEquiv : DiscreteCoind G U (DiscreteCoind U V A) ≃+ DiscreteCoind G W A where
  toFun f := mk G W A (fun g => f g 1)
    ((isLocallyConstant f).comp fun ψ : DiscreteCoind U V A => ψ 1)
    (fun w g => by
      -- `w` is the image of some `v : V`, and `f` is `U`-equivariant while `f g` is `V`-equivariant
      obtain ⟨x, hx, hv⟩ := Subgroup.mem_map.1 (hW ▸ w.2 : (w : G) ∈ V.map U.subtype)
      rw [Subgroup.subtype_apply] at hv
      rw [← hv, apply_mul f x g, coe_smul, one_mul, apply_coe (f g) ⟨x, hx⟩,
        hsmul ⟨x, hx⟩ w _ hv])
  invFun φ := mk G U (DiscreteCoind U V A)
    (fun g => mk U V A (fun u => φ ((u : G) * g))
      ((isLocallyConstant φ).comp_continuous (continuous_subtype_val.mul continuous_const))
      (fun v u => by
        have hvW : ((v : U) : G) ∈ W :=
          hW ▸ Subgroup.mem_map.2 ⟨v, v.2, Subgroup.subtype_apply (v : U)⟩
        rw [Subgroup.coe_mul, mul_assoc, apply_mul φ ⟨_, hvW⟩ ((u : G) * g)]
        exact hsmul v _ _ rfl))
    ((IsLocallyConstant.iff_exists_open _).2 fun g => by
      -- `φ` is locally constant under right translation uniformly in `u ∈ U`, the closure of `U`
      -- being compact
      obtain ⟨N, hN, hgN, h⟩ :=
        exists_isOpen_forall_mem_mul_right_eq (isLocallyConstant φ) hU continuous_id g
      exact ⟨N, hN, hgN, fun g' hg' => ext fun u => by
        rw [mk_apply, mk_apply]; exact h g' hg' u (subset_closure u.2)⟩)
    (fun u₀ g => ext fun u => by
      simp only [mk_apply, coe_smul, Subgroup.coe_mul, mul_assoc])
  left_inv f := ext fun g => ext fun u => by
    rw [mk_apply, mk_apply, mk_apply, apply_mul f u g, coe_smul, one_mul]
  right_inv φ := ext fun g => by
    simp only [mk_apply, Subgroup.coe_one, one_mul]
  map_add' f f' := ext fun g => by
    simp only [mk_apply, coe_add, Pi.add_apply]

/-- The transitivity equivalence evaluates the inner coinduced function at `1`. -/
@[simp]
theorem transEquiv_apply (f : DiscreteCoind G U (DiscreteCoind U V A)) (g : G) :
    transEquiv hW hsmul hU f g = f g 1 := (rfl)

/-- The inverse of the transitivity equivalence translates the argument by `U`. -/
@[simp]
theorem transEquiv_symm_apply (φ : DiscreteCoind G W A) (g : G) (u : U) :
    (transEquiv hW hsmul hU).symm φ g u = φ ((u : G) * g) := (rfl)

/-- The transitivity equivalence is `G`-equivariant for the right-translation actions. -/
@[simp]
theorem transEquiv_smul (g₀ : G) (f : DiscreteCoind G U (DiscreteCoind U V A)) :
    transEquiv hW hsmul hU (g₀ • f) = g₀ • transEquiv hW hsmul hU f := ext fun g => by
  rw [transEquiv_apply, coe_smul, coe_smul, transEquiv_apply]

/-- The inverse of the transitivity equivalence is `G`-equivariant. -/
@[simp]
theorem transEquiv_symm_smul (g₀ : G) (φ : DiscreteCoind G W A) :
    (transEquiv hW hsmul hU).symm (g₀ • φ) = g₀ • (transEquiv hW hsmul hU).symm φ :=
  (transEquiv hW hsmul hU).injective <| by
    rw [transEquiv_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The transitivity equivalence is compatible with the counits: evaluating the one-step coinduced
function at `1` is evaluating the two-step one at `1` twice. -/
theorem eval_transEquiv (f : DiscreteCoind G U (DiscreteCoind U V A)) :
    eval G W A (transEquiv hW hsmul hU f) = eval U V A (eval G U (DiscreteCoind U V A) f) := by
  rw [eval_apply, eval_apply, eval_apply, transEquiv_apply]

end Transitivity

section TopRep

open CategoryTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} {V : Subgroup U} {W : Subgroup G}
  {A : Type*} [AddCommGroup A] [DistribMulAction V A] [DistribMulAction W A]
  (hW : V.map U.subtype = W)
  (hsmul : ∀ (v : V) (w : W) (a : A), ((v : U) : G) = (w : G) → w • a = v • a)
  (hU : IsCompact (closure (U : Set G)))

/-- **Transitivity of coinduction as an isomorphism of topological representations**: the
canonical objects of `TopRep ℤ G` attached to `Coind_U^G (Coind_V^U A)` and to `Coind_W^G A` are
isomorphic, by `TauCeti.DiscreteCoind.transEquiv` on underlying modules. Applying continuous
cohomology to it identifies `Hⁿ(G, Coind_U^G (Coind_V^U A))` with `Hⁿ(G, Coind_W^G A)`. -/
noncomputable def transIso :
    ofDiscreteModule ℤ G (DiscreteCoind G U (DiscreteCoind U V A)) ≅
      ofDiscreteModule ℤ G (DiscreteCoind G W A) where
  hom := ofDiscreteModuleMap (transEquiv hW hsmul hU).toAddMonoidHom.toIntLinearMap fun g f =>
    transEquiv_smul hW hsmul hU g f
  inv := ofDiscreteModuleMap (transEquiv hW hsmul hU).symm.toAddMonoidHom.toIntLinearMap fun g φ =>
    transEquiv_symm_smul hW hsmul hU g φ
  -- After extensionality both laws are those of `transEquiv` on the underlying modules.
  hom_inv_id := by
    ext f
    exact (transEquiv hW hsmul hU).symm_apply_apply f
  inv_hom_id := by
    ext φ
    exact (transEquiv hW hsmul hU).apply_symm_apply φ

/-- The transitivity isomorphism acts on underlying modules as `transEquiv`. -/
@[simp]
theorem transIso_hom_apply (f : DiscreteCoind G U (DiscreteCoind U V A)) :
    (transIso hW hsmul hU).hom f = transEquiv hW hsmul hU f :=
  ofDiscreteModuleMap_hom_apply _ (fun g f => transEquiv_smul hW hsmul hU g f) f

/-- The inverse of the transitivity isomorphism acts on underlying modules as
`transEquiv.symm`. -/
@[simp]
theorem transIso_inv_apply (φ : DiscreteCoind G W A) :
    (transIso hW hsmul hU).inv φ = (transEquiv hW hsmul hU).symm φ :=
  ofDiscreteModuleMap_hom_apply _ (fun g φ => transEquiv_symm_smul hW hsmul hU g φ) φ

/-! ### The trivial subgroup -/

omit [TopologicalSpace G] [IsTopologicalGroup G] in
variable (U) in
/-- Two actions of trivial subgroups on the same module agree: a trivial group acts trivially. This
discharges the agreement hypothesis of `TauCeti.DiscreteCoind.transEquiv` at `V = ⊥` and `W = ⊥`. -/
theorem bot_smul_eq_bot_smul [DistribMulAction (⊥ : Subgroup U) A]
    [DistribMulAction (⊥ : Subgroup G) A] (v : (⊥ : Subgroup U)) (w : (⊥ : Subgroup G)) (a : A)
    (_ : ((v : U) : G) = (w : G)) : w • a = v • a := by
  rw [Subsingleton.elim v 1, Subsingleton.elim w 1, one_smul, one_smul]

variable (U A) in
include hU in
/-- **Transitivity of coinduction for the trivial subgroup**:
`Coind_U^G (Coind_1^U A) ≅ Coind_1^G A` as topological `G`-representations, the case `V = W = ⊥` of
`TauCeti.DiscreteCoind.transIso`. Dimension shifting uses this identification of coefficient
modules together with a separate acyclicity result for `Coind_1^G A` to pass Shapiro's lemma from
one degree to the next. -/
noncomputable def transIsoBot [DistribMulAction (⊥ : Subgroup U) A]
    [DistribMulAction (⊥ : Subgroup G) A] :
    ofDiscreteModule ℤ G (DiscreteCoind G U (DiscreteCoind U (⊥ : Subgroup U) A)) ≅
      ofDiscreteModule ℤ G (DiscreteCoind G (⊥ : Subgroup G) A) :=
  transIso (Subgroup.map_bot U.subtype) (bot_smul_eq_bot_smul U) hU

-- The carrier of `ofDiscreteModule ℤ G M` is `M` by definition, but only the `show` makes the
-- coinduced function applicable to a group element.
/-- The trivial-subgroup transitivity isomorphism evaluates the inner coinduced function at `1`. -/
@[simp]
theorem transIsoBot_hom_apply [DistribMulAction (⊥ : Subgroup U) A]
    [DistribMulAction (⊥ : Subgroup G) A]
    (f : DiscreteCoind G U (DiscreteCoind U (⊥ : Subgroup U) A)) (g : G) :
    (show DiscreteCoind G (⊥ : Subgroup G) A from (transIsoBot U A hU).hom f) g = f g 1 := by
  rw [transIsoBot, transIso_hom_apply, transEquiv_apply]

/-- The inverse of the trivial-subgroup transitivity isomorphism translates the argument by `U`. -/
@[simp]
theorem transIsoBot_inv_apply [DistribMulAction (⊥ : Subgroup U) A]
    [DistribMulAction (⊥ : Subgroup G) A] (φ : DiscreteCoind G (⊥ : Subgroup G) A) (g : G)
    (u : U) :
    (show DiscreteCoind G U (DiscreteCoind U (⊥ : Subgroup U) A) from
      (transIsoBot U A hU).inv φ) g u = φ ((u : G) * g) := by
  rw [transIsoBot, transIso_inv_apply, transEquiv_symm_apply]

end TopRep

end TauCeti.DiscreteCoind

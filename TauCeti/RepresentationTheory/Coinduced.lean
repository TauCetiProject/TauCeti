/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.OfMulAction
public import TauCeti.GroupTheory.GroupAction.PiTransport

/-!
# Coinduction: exactness and coextension of scalars

Coinduction along a subgroup preserves short exact sequences of representations. Unlike
coinduction along an arbitrary homomorphism, subgroup coinduction preserves epimorphisms;
together with its right adjoint structure this gives exactness, without a finite-index
assumption. This allows connecting maps to be compared through Shapiro's isomorphism.

On the module side, coinduction along a monoid homomorphism `φ : H →* G` is coextension of
scalars along `MonoidAlgebra.mapDomainRingHom k φ : k[H] →+* k[G]`: the `k[G]`-module
`Hom_{k[H]}(k[G], V)` of Mathlib's `ModuleCat.coextendScalars` is isomorphic to the module of
Mathlib's coinduced representation `Representation.coind φ ρ`, by evaluation at the
monoid elements (`Representation.coextendScalarsEquivCoind`). This transports statements about
coextension of scalars on module categories, such as its action on Grothendieck groups of group
algebras, to coinduced and induced representations.

If a representation `B` of `G` decomposes as a product whose factors `G` permutes transitively,
the map from `B` to the representation coinduced from the stabilizer of one factor, adjoint to the
projection to that factor, is bijective (`TauCeti.resCoindToHom_bijective_of_transport`). This
identifies the units of a semi-local algebra `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w` with a representation
coinduced from a decomposition group.

Mathlib's coinduced action is evaluated by `Representation.coind_apply_coe_apply`:
`(h • f) h₁ = f (h₁ * h)`. Coinduction along an open map whose image has finite index preserves
representations with open kernel (`Representation.isOpen_ker_coind`): the kernel of the
coinduced action contains the open set of `x` with `t x t⁻¹ ∈ φ(ker ρ)` for `t` in a finite set of
coset representatives.

`Representation.coindSupport` gives the support modulo a subgroup in the ordinary coset space.
The action on this support is described by `Representation.coindSupport_coind_apply` using
Mathlib's left action on cosets.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §6 and §9.
-/

public section

open CategoryTheory

namespace Rep

universe u v w t

variable {R : Type u} [CommRing R]

/-- Coinduction acts additively on coefficient maps. -/
instance {G : Type v} {H : Type w} [Monoid G] [Monoid H] (φ : H →* G) :
    (coindFunctor.{t} R φ).Additive where
  map_add := by intro X Y f g; ext x; rfl

/-- The counit of restriction–coinduction along a monoid homomorphism evaluates at `1`. -/
theorem resCoindAdjunction_counit_app_hom_apply
    {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Monoid G] [Monoid H]
    (φ : G →* H) (A : Rep.{max w t} k G) (f : Rep.coind φ A) :
    ((Rep.resCoindAdjunction.{t} k φ).counit.app A).hom f = f.val 1 :=
  rfl

/-- The inverse restriction–coinduction reciprocity evaluates the coinduced function at `1`. -/
theorem resCoindHomEquiv_symm_hom_apply {k : Type u} {G : Type v} {H : Type w}
    [CommRing k] [Monoid G] [Monoid H] (φ : G →* H)
    (B : Rep.{max w t} k H) (A : Rep.{max w t} k G)
    (f : B ⟶ coind φ A) (b : B) :
    ((resCoindHomEquiv.{t, u, v, w} φ B A).symm f).hom b = (f.hom b).val 1 :=
  rfl

variable {G : Type v} [Group G]

/-- Subgroup coinduction preserves homology of short complexes of representations. -/
noncomputable instance (H : Subgroup G) :
    (coindFunctor.{max v t} R H.subtype).PreservesHomology :=
  (coindFunctor.{max v t} R H.subtype).preservesHomology_of_preservesEpis_and_kernels

/-- Subgroup coinduction is exact, so also preserves finite colimits. -/
instance (H : Subgroup G) :
    Limits.PreservesFiniteColimits (coindFunctor.{max v t} R H.subtype) :=
  (coindFunctor.{max v t} R H.subtype).preservesFiniteColimits_of_preservesHomology

end Rep

namespace Representation

section Apply

variable {k G H V : Type*} [Semiring k] [Monoid G] [Monoid H] [AddCommMonoid V] [Module k V]

-- Not `@[simp]`: simp first unfolds the action `coind φ ρ h` through `Representation.coind_apply`,
-- so the left-hand side is not in simp-normal form (`simpNF`).
/-- The coinduced action translates the argument of a function: `(h • f) h₁ = f (h₁ * h)`. -/
theorem coind_apply_coe_apply (φ : G →* H) (ρ : Representation k G V) (f : coindV φ ρ)
    (h h₁ : H) : ((coind φ ρ h) f).val h₁ = f.val (h₁ * h) :=
  rfl

end Apply

section Support

open Function

variable {A G V : Type*} [Semiring A] [Group G] [AddCommMonoid V] [Module A V]
  {H : Subgroup G} {σ : Representation A H V}

/-- Support modulo `H` of a left-covariant function. Inversion identifies its left `H`-orbits
with the ordinary cosets in `G ⧸ H`. -/
def coindSupport (f : σ.coindV H.subtype) : Set (G ⧸ H) :=
  (fun g : G ↦ (↑g⁻¹ : G ⧸ H)) '' support f.val

/-- The coset of `g⁻¹` lies in the support iff the function is nonzero at `g`. -/
@[simp]
theorem coindSupport_mk_inv_mem_iff {f : σ.coindV H.subtype} {g : G} :
    (↑g⁻¹ : G ⧸ H) ∈ coindSupport f ↔ f.val g ≠ 0 := by
  refine ⟨?_, fun hg ↦ ⟨g, hg, rfl⟩⟩
  rintro ⟨x, hx, heq⟩
  have h : x * g⁻¹ ∈ H := by
    simpa only [inv_inv] using QuotientGroup.eq.mp heq
  have hcov := f.property ⟨x * g⁻¹, h⟩ g
  simp only [Subgroup.subtype_apply, inv_mul_cancel_right] at hcov
  intro hg
  exact hx (hcov.trans (by rw [hg, map_zero]))

/-- Quotient support is the image of ordinary function support under the inverse coset map. -/
theorem coindSupport_def (f : σ.coindV H.subtype) :
    coindSupport f = (fun g : G ↦ (↑g⁻¹ : G ⧸ H)) '' support f.val := (rfl)

/-- The zero function has empty support modulo the subgroup. -/
@[simp] theorem coindSupport_zero : coindSupport (0 : σ.coindV H.subtype) = ∅ := by
  simp only [coindSupport_def, Submodule.coe_zero, support_zero, Set.image_empty]

/-- Right translation on coinduction translates support by the left action on `G ⧸ H`. -/
theorem coindSupport_coind_apply (f : σ.coindV H.subtype) (g : G) :
    coindSupport (σ.coind H.subtype g f) = (g • ·) '' coindSupport f := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(↑(x * g)⁻¹ : G ⧸ H), coindSupport_mk_inv_mem_iff.2 ?_, ?_⟩
    · simpa only [mem_support, coind_apply_coe_apply] using hx
    · simp only [MulAction.Quotient.smul_coe, smul_eq_mul, mul_inv_rev, mul_inv_cancel_left]
  · rintro ⟨q, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x * g⁻¹, ?_, ?_⟩
    · simpa only [mem_support, coind_apply_coe_apply, inv_mul_cancel_right] using hx
    · simp only [MulAction.Quotient.smul_coe, smul_eq_mul, mul_inv_rev, inv_inv]

end Support

section OpenKernel

variable {k G H V : Type*} [Semiring k] [Group G] [Group H] [AddCommMonoid V] [Module k V]
  [TopologicalSpace G] [TopologicalSpace H] [SeparatelyContinuousMul H]

/-- **The coinduced action has open kernel.** If `φ : G →* H` is an open map whose image has
finite index and `ρ` has open kernel, the coinduced representation has open kernel: it contains
the open set of `x` with `t x t⁻¹ ∈ φ(ker ρ)` for `t` in a finite set of coset representatives. -/
theorem isOpen_ker_coind {φ : G →* H} (hφ : IsOpenMap φ) [φ.range.FiniteIndex]
    (ρ : Representation k G V) (hρ : IsOpen (ρ.ker : Set G)) :
    IsOpen ((coind φ ρ).ker : Set H) := by
  have : Finite (H ⧸ φ.range) := Subgroup.finite_quotient_of_finiteIndex
  let t : H ⧸ φ.range → H := fun c ↦ (Quotient.out c)⁻¹
  let S : Set H := ⋂ c, (fun x ↦ t c * x * (t c)⁻¹) ⁻¹' (φ '' (ρ.ker : Set G))
  have hS : IsOpen S := isOpen_iInter_of_finite fun c ↦
    (hφ _ hρ).preimage ((continuous_mul_const _).comp (continuous_const_mul _))
  have h1 : (1 : H) ∈ S := Set.mem_iInter.mpr fun c ↦ ⟨1, ρ.ker.one_mem, by simp⟩
  have hSK : S ⊆ (coind φ ρ).ker := by
    intro x hx
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    refine LinearMap.ext fun F ↦ Subtype.ext (funext fun y ↦ ?_)
    obtain ⟨⟨_, g, rfl⟩, hmk⟩ := QuotientGroup.mk_out_eq_mul φ.range y⁻¹
    set c : H ⧸ φ.range := QuotientGroup.mk y⁻¹
    have hy : y = φ g * t c := by
      simp only [t, c, hmk, mul_inv_rev, inv_inv, mul_inv_cancel_left]
    obtain ⟨g', hg', hg'x⟩ := Set.mem_iInter.mp hx c
    have hyx : y * x = φ (g * g') * t c := by
      rw [map_mul, hg'x, hy]
      group
    have hg'1 : ρ g' = 1 := MonoidHom.mem_ker.mp hg'
    calc F.val (y * x) = F.val (φ (g * g') * t c) := by rw [hyx]
      _ = ρ (g * g') (F.val (t c)) := F.property _ _
      _ = ρ g (F.val (t c)) := by rw [map_mul, hg'1, mul_one]
      _ = F.val y := by rw [← F.property, ← hy]
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hS.mem_nhds h1) hSK)

end OpenKernel

open scoped MonoidAlgebra

universe u v w

-- The carrier `V` lives in `Type (max u v)`, the universe of `k[G]`, as Mathlib's `Rep.coindIso`
-- requires.
variable {k : Type u} {H : Type w} {G : Type v} [CommRing k] [Monoid H] [Monoid G] (φ : H →* G)
  {V : Type (max u v)} [AddCommGroup V] [Module k V] (ρ : Representation k H V)

-- The explicit source type selects the restricted `k[H]`-action, so `x` is `k[H]`-linear.
private theorem coextendScalars_apply_mapDomain_mul
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) (r : k[H]) (a : k[G]) :
    ρ.asModuleEquiv (x (MonoidAlgebra.mapDomainRingHom k φ r * a)) =
      ρ.asAlgebraHom r (ρ.asModuleEquiv (x a)) :=
  congrArg ρ.asModuleEquiv (map_smul (ModuleCat.CoextendScalars.equiv _ _ x) r
    (show ↑((ModuleCat.restrictScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[G] k[G])) from a))

/-- `k[G]` acts on the coinduced representation `Representation.coind' φ A`, whose elements are
the morphisms `Rep.res φ (Rep.leftRegular k G) ⟶ A`, by right multiplication on the source
`k[G]`. -/
@[simp↓]
theorem coind'_asAlgebraHom_hom_apply (A : Rep k H) (r : k[G])
    (f : Rep.res φ (Rep.leftRegular k G) ⟶ A) (a : k[G]) :
    ((coind' φ A).asAlgebraHom r f).hom a = f.hom (a * r) := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    rw [MonoidAlgebra.of_apply, asAlgebraHom_single_one, coind'_apply_apply,
      Rep.hom_comp, IntertwiningMap.comp_apply]
    apply congrArg f.hom
    rw [← IntertwiningMap.toLinearMap_apply, Rep.resMap_hom_toLinearMap,
      IntertwiningMap.toLinearMap_apply, LinearEquiv.coe_coe,
      Rep.leftRegularHomEquiv_symm_apply]
  | add r r' hr hr' => simp [Rep.add_hom, hr, hr', mul_add]
  | smul c r hr =>
    simp only [map_smul, LinearMap.smul_apply, Rep.smul_hom, IntertwiningMap.coe_smul,
      Pi.smul_apply, mul_smul_comm, hr]

/-- A `k[H]`-linear map `k[G] → V` is an `H`-equivariant `k`-linear map from the restriction of
the left regular representation of `G`. -/
private noncomputable def coextendScalarsEquivCoind' :
    (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule) ≃ₗ[k[G]] (Rep.coind' φ (Rep.of ρ)).ρ.asModule where
  toFun x := Rep.ofHom
    { toFun a := ρ.asModuleEquiv (x a)
      map_add' a b := congrArg ρ.asModuleEquiv (map_add (ModuleCat.CoextendScalars.equiv _ _ x)
        (show ↑((ModuleCat.restrictScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
          (ModuleCat.of k[G] k[G])) from a) b)
      map_smul' c a := by
        -- `k`-linearity is `k[H]`-linearity at the scalars `single 1 c`.
        have : c • a = MonoidAlgebra.mapDomainRingHom k φ (.single 1 c) * a := by
          ext; simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_single_one_mul]
        rw [this, coextendScalars_apply_mapDomain_mul, asAlgebraHom_single, map_one]
        rfl
      isIntertwining' h := LinearMap.ext fun a ↦ by
        have := coextendScalars_apply_mapDomain_mul φ ρ x (.single h 1) a
        rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
          TauCeti.single_mul_eq_smul_ofMulAction, one_smul, asAlgebraHom_single_one] at this
        exact this }
  invFun f := (ModuleCat.CoextendScalars.equiv _ _).symm
    { toFun a := ρ.asModuleEquiv.symm (f.hom a)
      map_add' := map_add f.hom.toLinearMap
      map_smul' r a := by
        -- `r : k[H]` acts on the source `k[G]` through `mapDomainRingHom k φ`, and on the target
        -- through `ρ.asAlgebraHom`.
        change f.hom (MonoidAlgebra.mapDomainRingHom k φ r * show k[G] from a) =
          ρ.asAlgebraHom r (f.hom a)
        induction r using MonoidAlgebra.induction_linear with
        | zero => rw [map_zero, zero_mul, map_zero, map_zero, LinearMap.zero_apply]
        | add r r' hr hr' => rw [map_add, add_mul, map_add, hr, hr', map_add, LinearMap.add_apply]
        | single h c =>
          rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
            TauCeti.single_mul_eq_smul_ofMulAction, map_smul, asAlgebraHom_single]
          exact congrArg (c • ·) (Rep.hom_comm_apply f h a) }
  map_add' x y := rfl
  map_smul' r x := Rep.hom_ext <| IntertwiningMap.ext <| LinearMap.ext fun a ↦ by
    -- `r • f` in the module of `coind'` is `(coind' φ _).asAlgebraHom r f`.
    change _ = ((coind' φ (Rep.of ρ)).asAlgebraHom r _).hom a
    rw [coind'_asAlgebraHom_hom_apply]
    rfl
  left_inv x := rfl
  right_inv f := rfl

/-- **Coinduction is coextension of scalars.** For a monoid homomorphism `φ : H →* G` and a
representation `ρ` of `H` on `V`, the `k[G]`-module `Hom_{k[H]}(k[G], V)`, with `k[H]` acting on
`k[G]` through `φ`, is isomorphic to the module of Mathlib's coinduced representation
`Representation.coind φ ρ`: a homomorphism `x` corresponds to the function `g ↦ x (single g 1)`.
It is Mathlib's `Rep.coindIso` read through the identification of `k[H]`-linear maps
`k[G] → V` with the morphisms of `Rep.coind' φ`. -/
noncomputable def coextendScalarsEquivCoind :
    (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule) ≃ₗ[k[G]] (coind φ ρ).asModule :=
  (coextendScalarsEquivCoind' φ ρ).trans
    (TauCeti.Representation.asModuleLinearEquivOfEquiv
      (equivOfIso (Rep.coindIso φ (Rep.of ρ)).symm))

/-- `Representation.coextendScalarsEquivCoind` evaluates a homomorphism at the monoid elements. -/
@[simp]
theorem coextendScalarsEquivCoind_apply
    (x : (ModuleCat.coextendScalars (MonoidAlgebra.mapDomainRingHom k φ)).obj
      (ModuleCat.of k[H] ρ.asModule)) (g : G) :
    Subtype.val (p := (· ∈ coindV φ ρ)) (coextendScalarsEquivCoind φ ρ x) g =
      (x (.single g 1) : V) := by
  rw [coextendScalarsEquivCoind, LinearEquiv.trans_apply,
    TauCeti.Representation.asModuleLinearEquivOfEquiv_apply]
  rfl

/-- The inverse of `Representation.coextendScalarsEquivCoind` sends a coinduced function `y` to
the homomorphism taking the value `y g` at `single g 1`. -/
@[simp]
theorem coextendScalarsEquivCoind_symm_apply_single (y : (coind φ ρ).asModule) (g : G) :
    ((coextendScalarsEquivCoind φ ρ).symm y (.single g 1) : V) =
      Subtype.val (p := (· ∈ coindV φ ρ)) y g := by
  conv_rhs => rw [← (coextendScalarsEquivCoind φ ρ).apply_symm_apply y]
  rw [coextendScalarsEquivCoind_apply]

end Representation

namespace TauCeti

variable {G P ι : Type*} [Group G] [MulAction G P] {p : ι → P} {M : ι → Type*}
  (T : ∀ (g : G) {i j : ι}, p j = g • p i → M i ≃ M j) {w : ι}

/-- **Coinduction from a stabilizer.** Let `B` be a representation of `G` that decomposes as a
product `∏_{i : ι} M i` on which `g` carries the factor at `i` to the factor at `j` along
`T g : M i ≃ M j` whenever `p j = g • p i`, and let `A` be a representation of the stabilizer of
`p w` whose underlying type is identified with `M w` compatibly with a morphism `f : B ⟶ A` that is
the projection to the factor at `w`. If `G` permutes the factors transitively and every element
of `G` carries some factor to `w`, then the map `B ⟶ Coind A` adjoint to `f` is bijective. The
composition of the transport maps and the stabilizer action on `A` are then forced by `e`. -/
theorem resCoindToHom_bijective_of_transport {k : Type*} [CommRing k] {B : Rep k G}
    {A : Rep k (MulAction.stabilizer G (p w))}
    (f : Rep.res (MulAction.stabilizer G (p w)).subtype B ⟶ A) (e : B ≃ ∀ i, M i)
    (he : ∀ (g : G) (x : B) {i j : ι} (h : p j = g • p i), e (B.ρ g x) j = T g h (e x i))
    (eA : A ≃ M w) (hf : ∀ x, eA (f.hom x) = e x w)
    (htrans : ∀ i, ∃ g : G, p w = g • p i) (hsurj : ∀ g : G, ∃ i, p w = g • p i) :
    Function.Bijective (Rep.resCoindToHom _ B A f).hom := by
  classical
  -- every element of a factor is a component of some element of `B`
  have hcomp : ∀ (i : ι) (a : M i), ∃ x : B, e x i = a := fun i a ↦
    ⟨e.symm (Function.update (e 0) i a), by simp⟩
  have hT : ∀ (g g' : G) {i j k : ι} (h : p j = g • p i) (h' : p k = g' • p j) (a : M i),
      T g' h' (T g h a) = T (g' * g) (by rw [h', h, mul_smul]) a := by
    intro g g' i j k h h' a
    obtain ⟨x, rfl⟩ := hcomp i a
    rw [← he g x h, ← he g' _ h', ← he (g' * g) x _, map_mul]
    rfl
  have hA : ∀ (d : MulAction.stabilizer G (p w)) (a : A),
      eA (A.ρ d a) = T d (MulAction.mem_stabilizer_iff.mp d.property).symm (eA a) := by
    intro d a
    obtain ⟨x, hx⟩ := hcomp w (eA a)
    obtain rfl : f.hom x = a := eA.injective ((hf x).trans hx)
    have := Rep.hom_comm_apply f d x
    simp only [Rep.res_obj_ρ] at this
    rw [← this, hf, hf, MonoidHom.comp_apply, Subgroup.subtype_apply,
      he d.val x (MulAction.mem_stabilizer_iff.mp d.property).symm]
  refine ⟨fun x x' h ↦ e.eq_of_forall_transport_component_eq T he htrans fun g ↦ ?_,
    fun F ↦ ?_⟩
  · rw [← hf, ← hf]
    exact congrArg (fun F ↦ eA (F.val g)) h
  obtain ⟨x, hx⟩ := e.exists_forall_transport_component_eq T he hT htrans hsurj
    (fun g ↦ eA (F.val g)) fun d hd g ↦ by
      have hF := F.property ⟨d, MulAction.mem_stabilizer_iff.mpr hd.symm⟩ g
      simp only [Subgroup.subtype_apply] at hF
      rw [hF, hA]
  exact ⟨x, Subtype.ext <| funext fun g ↦ eA.injective <| (hf _).trans (hx g)⟩

end TauCeti

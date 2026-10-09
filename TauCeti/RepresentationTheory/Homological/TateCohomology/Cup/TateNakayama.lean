/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Delta
public import TauCeti.RepresentationTheory.Homological.TateCohomology.NakayamaRim
public import TauCeti.RepresentationTheory.Homological.TateCohomology.SplittingModule
import Mathlib.RingTheory.Flat.Equalizer

/-!
# The Tate–Nakayama theorem

Let `G` be a finite group, `C` a representation of `G` over `ℤ` and `u ∈ H²(G, C)`. Suppose that
for every subgroup `S` of `G` of prime-power order, `H¹(S, C) = 0`, the restriction of `u`
generates `H²(S, C)`, and `H²(S, C)` has `|S|` elements. Then for every representation `M` with
`Tor₁^ℤ(M, C) = 0`, cup product with `u` is a bijection

`H^r(G, M) → H^{r+2}(G, M ⊗ C)`

in every integer degree `r`
(`TauCeti.TateCohomology.cup_bijective_of_forall_isPGroup_of_lTensor_injective`). This is
Nakayama's generalization (*Cohomology of class field theory and tensor product modules I*,
Ann. of Math. 65 (1957)) of Tate's theorem, the case `M = ℤ`
(`TauCeti.TateCohomology.cup_bijective_of_forall_isPGroup`). As in
`Rep.isZero_res_tensor_of_isZero_res`, the vanishing of `Tor₁^ℤ(M, C)` is stated without a `Tor`
functor: `M ⊗ X → M ⊗ Y` is injective for every short exact sequence `0 → X → Y → C → 0` of
abelian groups. It holds for instance whenever `M` or `C` is torsion-free. Throughout this
file, `H^n(G, M)` denotes Tate cohomology in the integer degree `n`.

## Proof

The class `u` sits in two short exact sequences, both split over `ℤ`: the splitting-module sequence
`0 → C → C(u) → I_G → 0` (`Rep.splittingModule`) and the augmentation sequence
`0 → I_G → ℤ[G] → ℤ → 0`. The splitting module is cohomologically trivial under Tate's hypotheses
(`TauCeti.TateCohomology.isZero_res_splittingModule`), and so is `M ⊗ C(u)`: as an abelian group
`C(u)` is `I_G × C`, so `Tor₁^ℤ(M, C(u)) = Tor₁^ℤ(M, C) = 0`, and the theorem of Nakayama and Rim
applies (`TauCeti.TateCohomology.isZero_res_tensor_splittingModule`). Since `M ⊗ ℤ[G]` is induced,
both tensored sequences have bijective connecting maps `δ`. As `u` dies in `C(u)`, it is
`δ (δ z)` for some `z ∈ H⁰(G, ℤ) = ℤ/|G|`, and the rule `x ∪ δ y = (-1)^r δ (x ∪ y)` for `ℤ`-split
sequences (`TauCeti.TateCohomology.cup_δ_of_leftInverse`), applied twice, turns cup product with
`u` into `x ↦ δ (δ (x ∪ z))`. Finally `z` is the class of an integer prime to `|G|`: a prime
`p ∣ |G|` dividing it would make `u` restrict to zero on a subgroup of order `p`, whose `H²` it
generates and which has `p` elements. Such an integer is invertible in `H⁰(G, ℤ) = ℤ/|G|`, so cup
product with `z` is bijective, as cup product with the class of `1` is.

## Main statements

* `TauCeti.TateCohomology.isZero_res_tensor_splittingModule`: under Tate's hypotheses and
  `Tor₁(M, C) = 0`, the tensor product `M ⊗ C(u)` with the splitting module is cohomologically
  trivial.
* `TauCeti.TateCohomology.cup_bijective_of_forall_isPGroup_of_lTensor_injective`: the
  Tate–Nakayama theorem.

## References

* T. Nakayama, *Cohomology of class field theory and tensor product modules I*, Ann. of Math. 65
  (1957).
* J.-P. Serre, *Local Fields*, Chapter IX, §8.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §8.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory Rep

namespace TauCeti.TateCohomology

section SplitSequences

variable {k G : Type} [CommRing k] [Group G]

/-- The inclusion `C → C(u)` has the `k`-linear retraction `C(u) = I_G × C → C`. -/
private theorem leftInverse_splittingModuleIncl (C : Rep k G) (u : groupCohomology C 2) :
    Function.LeftInverse (LinearMap.snd k _ _ ∘ₗ (splittingModuleEquiv C u).toLinearMap)
      (splittingModuleIncl C u).hom := fun c ↦ by
  simp

/-- The inclusion `I_G → k[G]` has a `k`-linear retraction, since the augmentation has the
`k`-linear section `a ↦ a · 1`. -/
private theorem exists_leftInverse_augmentationι :
    ∃ r : (leftRegular k G).V →ₗ[k] (augmentationIdeal k G).V,
      Function.LeftInverse r (augmentationι k G).hom := by
  have hS := augmentationSES_shortExact k G
  rw [augmentationSES_def] at hS
  have := hS.mono_f
  exact Rep.exists_leftInverse_of_rightInverse hS.exact
    (s := (MonoidAlgebra.lsingle (R := k) (1 : G) : k →ₗ[k] MonoidAlgebra k G)) fun a ↦ by simp

/-- `Tor₁(M, C(u)) = 0` when `Tor₁(M, C) = 0`, both in the elementary form of
`Rep.isZero_res_tensor_of_isZero_res`. -/
private theorem lTensor_injective_splittingModule (C : Rep k G) (u : groupCohomology C 2)
    (M : Rep k G)
    (hM : ∀ {X Y : Type} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
      (f : X →ₗ[k] Y) (g : Y →ₗ[k] C.V), Function.Injective f → Function.Exact f g →
        Function.Surjective g → Function.Injective (f.lTensor M.V))
    {X Y : Type} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] (splittingModule C u).V) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Injective (f.lTensor M.V) := by
  -- As a `k`-module `C(u)` is `I_G × C`, so `0 → X → Y → C(u) → 0` restricts to
  -- `0 → X → Y' → C → 0`, where `Y'` is the kernel of `q : Y → I_G`. Tensoring with `M` keeps
  -- `X → Y'` injective by hypothesis, and `Y' → Y` injective because `I_G`, a direct summand of
  -- `k[G]`, is flat.
  obtain ⟨ra, hra⟩ := exists_leftInverse_augmentationι (k := k) (G := G)
  have : Module.Projective k (augmentationIdeal k G).V :=
    .of_split (augmentationι k G).hom.toLinearMap ra (LinearMap.ext hra)
  let e := (splittingModuleEquiv C u).toLinearMap ∘ₗ g
  let q : Y →ₗ[k] (augmentationIdeal k G).V := LinearMap.fst k _ _ ∘ₗ e
  have hq : Function.Surjective q := fun x ↦ by
    obtain ⟨y, hy⟩ := hg ((splittingModuleEquiv C u).symm (x, 0))
    exact ⟨y, by simp [q, e, hy]⟩
  have hfq (x : X) : f x ∈ LinearMap.ker q := by
    simp [q, e, hfg.apply_apply_eq_zero]
  let f' : X →ₗ[k] LinearMap.ker q := f.codRestrict _ hfq
  let g' : LinearMap.ker q →ₗ[k] C.V := LinearMap.snd k _ _ ∘ₗ e ∘ₗ (LinearMap.ker q).subtype
  -- On `ker q` the map `e` takes values in `0 × C`.
  have he (y : LinearMap.ker q) : e y = (0, g' y) := Prod.ext y.2 rfl
  have h' : Function.Injective (f'.lTensor M.V) := by
    refine hM f' g' (fun x y hxy ↦ hf (congrArg Subtype.val hxy)) (fun y ↦ ?_) (fun c ↦ ?_)
    · refine ⟨fun hy ↦ ?_, ?_⟩
      · have h0 : splittingModuleEquiv C u (g y) = (0, 0) := (he y).trans (by rw [hy])
        have : g y = 0 := (splittingModuleEquiv C u).injective (h0.trans (map_zero _).symm)
        obtain ⟨x, hx⟩ := (hfg y).1 this
        exact ⟨x, Subtype.ext hx⟩
      · rintro ⟨x, rfl⟩
        simp [g', e, f', hfg.apply_apply_eq_zero]
    · obtain ⟨y, hy⟩ := hg ((splittingModuleEquiv C u).symm (0, c))
      have hyq : y ∈ LinearMap.ker q := by simp [q, e, hy]
      exact ⟨⟨y, hyq⟩, by simp [g', e, hy]⟩
  have hY : Function.Injective ((LinearMap.ker q).subtype.lTensor M.V) :=
    LinearMap.lTensor_injective_of_exact_of_flat q hq _ Subtype.val_injective
      (LinearMap.exact_subtype_ker_map q) M.V
  have : f.lTensor M.V = ((LinearMap.ker q).subtype.lTensor M.V) ∘ₗ (f'.lTensor M.V) := by
    rw [← LinearMap.lTensor_comp]
    rfl
  rw [this, LinearMap.coe_comp]
  exact hY.comp h'

/-- **Tensoring the splitting module.** Let `k` be a principal ideal domain of characteristic zero
in which every prime number is a unit or generates a maximal ideal, `C` a representation of a
finite group `G` over `k` and `u ∈ H²(G, C)`. Suppose that for every subgroup `S` of `G` of
prime-power order, `H¹(S, C) = 0`, the restriction of `u` generates `H²(S, C)`, and `H²(S, C)` has
the finite order of `k ⧸ |S|k`. If `Tor₁^k(M, C) = 0`, in the form that `M ⊗ X → M ⊗ Y` is
injective for every short exact sequence `0 → X → Y → C → 0` of `k`-modules, then
`M ⊗ C(u)` is cohomologically trivial. -/
theorem isZero_res_tensor_splittingModule [Finite G] [IsDomain k] [IsPrincipalIdealRing k]
    [CharZero k] (hk : ∀ p : ℕ, p.Prime → IsUnit (p : k) ∨ (Ideal.span {(p : k)}).IsMaximal)
    (C : Rep k G) (u : groupCohomology C 2)
    (h1 : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (hgen : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      ∀ x : groupCohomology (Rep.res S.subtype C) 2,
        ∃ r : k, r • groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2 u = x)
    (hfin : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      Finite (k ⧸ Ideal.span {(Nat.card S : k)}))
    (hcard : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      Nat.card (groupCohomology (Rep.res S.subtype C) 2) =
        Nat.card (k ⧸ Ideal.span {(Nat.card S : k)}))
    (M : Rep k G)
    (hM : ∀ {X Y : Type} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
      (f : X →ₗ[k] Y) (g : Y →ₗ[k] C.V), Function.Injective f → Function.Exact f g →
        Function.Surjective g → Function.Injective (f.lTensor M.V))
    (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (Rep.res S.subtype (M ⊗ splittingModule C u)) n) :=
  Rep.isZero_res_tensor_of_isZero_res hk (splittingModule C u)
    (isZero_res_splittingModule C u h1 hgen hfin hcard) M
    (fun f g hf hfg hg ↦ lTensor_injective_splittingModule C u M hM f g hf hfg hg) S n

end SplitSequences

section TateNakayama

section Sequences

variable {G : Type} [Group G]

/-- The splitting-module sequence `0 → C → C(u) → I_G → 0`, with its maps named because the body
of `Rep.splittingModuleSES` is not exposed. -/
private abbrev splittingSES (C : Rep ℤ G) (u : groupCohomology C 2) : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (splittingModuleIncl C u) (splittingModuleProj C u)
    (splittingModuleIncl_comp_splittingModuleProj C u)

private theorem shortExact_splittingSES (C : Rep ℤ G) (u : groupCohomology C 2) :
    (splittingSES C u).ShortExact := by
  simpa only [splittingModuleSES_def] using splittingModuleSES_shortExact C u

/-- The augmentation sequence `0 → I_G → ℤ[G] → ℤ → 0`, presented as `Rep.augmentationSES` is by
`Rep.augmentationSES_def`, so that its first map is literally `augmentationι`. -/
private abbrev augSES : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (augmentationι ℤ G) (augmentation ℤ G) (augmentationι_comp_augmentation ℤ G)

private theorem shortExact_augSES : (augSES (G := G)).ShortExact := by
  simpa only [augmentationSES_def] using augmentationSES_shortExact ℤ G

end Sequences

variable {G : Type} [Group G] [Fintype G]

/-- The connecting map of a short exact sequence is bijective in degree `n` when the middle term
has no Tate cohomology in degrees `n` and `n + 1`. -/
private theorem δ_bijective {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact) (n : ℤ)
    (h₀ : IsZero (tateCohomology S.X₂ n)) (h₁ : IsZero (tateCohomology S.X₂ (n + 1))) :
    Function.Bijective (_root_.TateCohomology.δ hS n) :=
  ConcreteCategory.bijective_of_isIso
    ((_root_.TateCohomology.map_tateComplexFunctor_shortExact hS).δIso n (n + 1) rfl h₀ h₁).hom

omit [Fintype G] in
/-- If a class `u` whose restriction to every subgroup `S` of prime-power order generates
`H²(S, C)`, a group with `|S|` elements, is a multiple `m • w`, then no prime divisor of `|G|`
divides `m`. -/
private theorem not_dvd_of_eq_zsmul [Finite G] (C : Rep ℤ G) (u : groupCohomology C 2)
    (hgen : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      ∀ x : groupCohomology (Rep.res S.subtype C) 2,
        ∃ m : ℤ, m • groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2 u = x)
    (hcard : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Nat.card S)
    {m : ℤ} {w : groupCohomology C 2} (huw : u = m • w)
    (p : ℕ) (hp : p.Prime) (hpG : p ∣ Nat.card G) : ¬ (p : ℤ) ∣ m := by
  -- Otherwise `u` restricts to `(m / p) • p • w = 0` on a subgroup `P` of order `p`, so it cannot
  -- generate `H²(P, C)`, which has `p` elements.
  rintro ⟨m', hm'⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpG
  let P := Subgroup.zpowers g
  have hP : Nat.card P = p := (Nat.card_zpowers g).trans hg
  have hPp : IsPGroup p P := IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
  have hpw : (p : ℤ) • groupCohomology.map P.subtype (𝟙 (Rep.res P.subtype C)) 2 w = 0 := by
    rw [natCast_zsmul, ← hP]
    exact groupCohomology.natCard_nsmul_eq_zero (n := 1) _
  have hres : groupCohomology.map P.subtype (𝟙 (Rep.res P.subtype C)) 2 u = 0 := by
    rw [huw, map_zsmul, hm', mul_zsmul', hpw, zsmul_zero]
  have hsub : Subsingleton (groupCohomology (Rep.res P.subtype C) 2) :=
    ⟨fun a b ↦ by
      obtain ⟨n, rfl⟩ := hgen p P hPp a
      obtain ⟨n', rfl⟩ := hgen p P hPp b
      rw [hres, zsmul_zero, zsmul_zero]⟩
  have hcardP := hcard p P hPp
  rw [Nat.card_unique, hP] at hcardP
  exact hp.one_lt.ne hcardP

/-- The class `u` is `δ (δ z)` for the connecting maps `H⁰(ℤ) → H¹(I_G) → H²(C)` and the class
`z` of an invariant of `ℤ`. -/
private theorem exists_eq_δ_δ (C : Rep ℤ G) (u : groupCohomology C 2) :
    ∃ y : (Rep.trivial ℤ G ℤ).ρ.invariants,
      ((_root_.TateCohomology.isoGroupCohomology 2).app C).inv u =
        _root_.TateCohomology.δ (shortExact_splittingSES C u) 1
          (_root_.TateCohomology.δ shortExact_augSES 0 (H0π _ y)) := by
  -- `u` dies in `C(u)`, so it is `δ e` for some `e ∈ H¹(I_G)`; and `δ : H⁰(ℤ) → H¹(I_G)` is onto.
  have hι : (tateCohomologyFunctor 2).map (splittingModuleIncl C u)
      (((_root_.TateCohomology.isoGroupCohomology 2).app C).inv u) = 0 := by
    have hnat := (ConcreteCategory.congr_hom
      ((_root_.TateCohomology.isoGroupCohomology 2).inv.naturality (splittingModuleIncl C u)) u)
    refine hnat.symm.trans ?_
    -- `groupCohomology.functor` acts on morphisms by `groupCohomology.map (MonoidHom.id G)`, by
    -- definition; restate the left side in that form to apply `map_splittingModuleIncl_eq_zero`.
    change ((_root_.TateCohomology.isoGroupCohomology 2).app _).inv
      (groupCohomology.map (MonoidHom.id G) (splittingModuleIncl C u) 2 u) = 0
    rw [map_splittingModuleIncl_eq_zero]
    exact map_zero _
  obtain ⟨e, he⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (_root_.TateCohomology.exact₁ (shortExact_splittingSES C u) 1) _ hι
  obtain ⟨z, rfl⟩ := ((_root_.TateCohomology.map_tateComplexFunctor_shortExact
    shortExact_augSES).δIso 0 (0 + 1) rfl (isZero_leftRegular 0)
      (isZero_leftRegular _)).toLinearEquiv.surjective e
  obtain ⟨y, rfl⟩ : ∃ y, H0π _ y = z :=
    H0_induction_on (C := fun z ↦ ∃ y, H0π _ y = z) z fun y ↦ ⟨y, rfl⟩
  exact ⟨y, he.symm⟩

variable (M : Rep ℤ G)

/-- **Cup product with `δ (δ z)`.** Tensoring the splitting-module and augmentation sequences with
`M` keeps them short exact, and `x ∪ δ (δ z) = δ (δ (x ∪ z))`: by
`TauCeti.TateCohomology.cup_δ_of_leftInverse`, each connecting map contributes the sign
`(-1)^r`. -/
private theorem cup_δ_δ (C : Rep ℤ G) (u : groupCohomology C 2) {r : ℤ}
    (x : tateCohomology M r) (z : tateCohomology (Rep.trivial ℤ G ℤ) 0) :
    haveI := (shortExact_splittingSES C u).epi_g
    haveI := (shortExact_augSES (G := G)).epi_g
    cup M C r 2 (r + 1 + 1) (by omega) x (_root_.TateCohomology.δ (shortExact_splittingSES C u) 1
        (_root_.TateCohomology.δ shortExact_augSES 0 z)) =
      _root_.TateCohomology.δ (Rep.shortExact_map_tensorLeft_of_leftInverse
          (shortExact_splittingSES C u).exact M (leftInverse_splittingModuleIncl C u)) (r + 1)
        (_root_.TateCohomology.δ (Rep.shortExact_map_tensorLeft_of_leftInverse
            shortExact_augSES.exact M (exists_leftInverse_augmentationι (k := ℤ)).choose_spec) r
          (cupH0 M (Rep.trivial ℤ G ℤ) r x z)) := by
  have := (shortExact_splittingSES C u).epi_g
  have := (shortExact_augSES (G := G)).epi_g
  have Ts := Rep.shortExact_map_tensorLeft_of_leftInverse (shortExact_splittingSES C u).exact M
    (leftInverse_splittingModuleIncl C u)
  have Ta := Rep.shortExact_map_tensorLeft_of_leftInverse shortExact_augSES.exact M
    (exists_leftInverse_augmentationι (k := ℤ) (G := G)).choose_spec
  calc cup M C r 2 (r + 1 + 1) (by omega) x
        (_root_.TateCohomology.δ (shortExact_splittingSES C u) 1
          (_root_.TateCohomology.δ shortExact_augSES 0 z))
      = r.negOnePow • _root_.TateCohomology.δ Ts (r + 1)
          (cup M (augmentationIdeal ℤ G) r (0 + 1) (r + 1) (by omega) x
            (_root_.TateCohomology.δ shortExact_augSES 0 z)) :=
        cup_δ_of_leftInverse M (shortExact_splittingSES C u) (leftInverse_splittingModuleIncl C u)
          (p := r) (q := 1) (n := r + 1) rfl x _
    _ = r.negOnePow • _root_.TateCohomology.δ Ts (r + 1) (r.negOnePow •
          _root_.TateCohomology.δ Ta r (cup M (Rep.trivial ℤ G ℤ) r 0 r (add_zero r) x z)) := by
        rw [cup_δ_of_leftInverse M shortExact_augSES
          (exists_leftInverse_augmentationι (k := ℤ) (G := G)).choose_spec (add_zero r) x]
    _ = _ := by
        rw [Units.smul_def, Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul,
          Int.units_mul_self, Units.val_one, one_smul, cup_zero_right]

/-- Cup product with an integer `m` prime to `|G|`, read as a class of `H⁰(G, ℤ) = ℤ/|G|`, is
bijective. -/
private theorem cupH0_zsmul_bijective {r : ℤ} {m : ℤ}
    (hm : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → ¬ (p : ℤ) ∣ m) :
    Function.Bijective fun x : tateCohomology M r ↦
      cupH0 M (Rep.trivial ℤ G ℤ) r x (m • trivialTateHZeroOne G) := by
  -- Cup product with the class of `1` is induced by the isomorphism `x ↦ x ⊗ 1`.
  let one : (Rep.trivial ℤ G ℤ).ρ.invariants := ⟨1, by simp [Representation.invariants]⟩
  have : IsIso (Rep.tensorInvariant M one ≫ (β_ M (Rep.trivial ℤ G ℤ)).hom ≫ (λ_ M).hom) := by
    rw [Rep.tensorInvariant_one_braiding_leftUnitor M]
    infer_instance
  have := IsIso.of_isIso_comp_right (Rep.tensorInvariant M one)
    ((β_ M (Rep.trivial ℤ G ℤ)).hom ≫ (λ_ M).hom)
  have hone : Function.Bijective fun x : tateCohomology M r ↦
      cupH0 M (Rep.trivial ℤ G ℤ) r x (trivialTateHZeroOne G) := by
    have : (fun x : tateCohomology M r ↦ cupH0 M (Rep.trivial ℤ G ℤ) r x (trivialTateHZeroOne G)) =
        (tateCohomologyFunctor r).map (Rep.tensorInvariant M one) :=
      funext fun x ↦ by rw [trivialTateHZeroOne_def, cupH0_H0π]
    rw [this]
    exact ConcreteCategory.bijective_of_isIso _
  -- `m` is invertible modulo `|G|`, and `|G|` kills the class of `1`.
  obtain ⟨a, b, hab⟩ : IsCoprime m (Nat.card G : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact Nat.Coprime.symm <| Nat.coprime_of_dvd fun p hp hpG hpm ↦
      hm p hp hpG (Int.natCast_dvd.2 hpm)
  have ha : a • m • trivialTateHZeroOne G = trivialTateHZeroOne G := by
    apply (H0LinearEquivTrivialIntZModCard G).injective
    rw [map_zsmul, map_zsmul, H0LinearEquivTrivialIntZModCard_trivialTateHZeroOne, smul_smul,
      zsmul_one, show a * m = 1 - b * Nat.card G by linarith]
    push_cast
    rw [ZMod.natCast_self, mul_zero, sub_zero]
  -- Multiplication by `m` on the target is therefore inverted by multiplication by `a`.
  have key (t : tateCohomology (M ⊗ Rep.trivial ℤ G ℤ) r) : a • m • t = t := by
    obtain ⟨x, rfl⟩ := hone.2 t
    simp only
    rw [← map_zsmul, ← map_zsmul, ha]
  have hm' : Function.Bijective fun t : tateCohomology (M ⊗ Rep.trivial ℤ G ℤ) r ↦ m • t :=
    Function.bijective_iff_has_inverse.2 ⟨fun t ↦ a • t, key, fun t ↦ by
      simp only
      rw [← mul_zsmul', mul_zsmul, key]⟩
  have hmap : (fun x : tateCohomology M r ↦
      cupH0 M (Rep.trivial ℤ G ℤ) r x (m • trivialTateHZeroOne G)) =
        (fun t ↦ m • t) ∘ fun x ↦ cupH0 M (Rep.trivial ℤ G ℤ) r x (trivialTateHZeroOne G) :=
    funext fun x ↦ map_zsmul _ m _
  rw [hmap]
  exact hm'.comp hone

/-- **The Tate–Nakayama theorem** (Nakayama, Ann. of Math. 65 (1957); Serre, *Local Fields*, IX §8).
Let `G` be a finite group, `C` a representation of `G` over `ℤ` and `u ∈ H²(G, C)`.
Suppose that for every subgroup `S` of `G` of prime-power order

* `H¹(S, C) = 0`,
* the restriction of `u` generates `H²(S, C)`, and
* `H²(S, C)` has `|S|` elements.

Then for every representation `M` with `Tor₁^ℤ(M, C) = 0`, in the form that `M ⊗ X → M ⊗ Y` is
injective for every short exact sequence `0 → X → Y → C → 0` of abelian groups, cup product with
`u` is a bijection `H^r(G, M) → H^{r+2}(G, M ⊗ C)` in every integer degree `r`. -/
theorem cup_bijective_of_forall_isPGroup_of_lTensor_injective (C : Rep ℤ G)
    (u : groupCohomology C 2)
    (h1 : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (hgen : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      ∀ x : groupCohomology (Rep.res S.subtype C) 2,
        ∃ m : ℤ, m • groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2 u = x)
    (hcard : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G), IsPGroup p S →
      Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Nat.card S)
    (hM : ∀ {X Y : Type} [AddCommGroup X] [Module ℤ X] [AddCommGroup Y] [Module ℤ Y]
      (f : X →ₗ[ℤ] Y) (g : Y →ₗ[ℤ] C.V), Function.Injective f → Function.Exact f g →
        Function.Surjective g → Function.Injective (f.lTensor M.V))
    (r r' : ℤ) (h : r + 2 = r') :
    Function.Bijective fun x : tateCohomology M r ↦
      cup M C r 2 r' h x (((_root_.TateCohomology.isoGroupCohomology 2).app C).inv u) := by
  obtain rfl : r' = r + 1 + 1 := by omega
  -- `M ⊗ C(u)` is cohomologically trivial, and so is the induced representation `M ⊗ ℤ[G]`.
  have hMCu (n : ℤ) : IsZero (tateCohomology (M ⊗ splittingModule C u) n) := by
    have hcardZ (n : ℕ) [NeZero n] : Nat.card (ℤ ⧸ Ideal.span {(n : ℤ)}) = n :=
      (Nat.card_congr (Int.quotientSpanNatEquivZMod n).toEquiv).trans (Nat.card_zmod n)
    let _ : Fintype (⊤ : Subgroup G) := Fintype.ofFinite _
    refine (isZero_res_tensor_splittingModule (fun p hp ↦ .inr
      (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible))
      C u h1 (fun p _ S hS x ↦ (hgen p S hS x).imp fun m hm ↦ (int_smul_eq_zsmul _ m _).trans hm)
      (fun _ _ S _ ↦ Finite.of_equiv _ (Int.quotientSpanNatEquivZMod (Nat.card S)).toEquiv.symm)
      (fun p _ S hS ↦ (hcard p S hS).trans (hcardZ _).symm) M hM ⊤ n).of_iso ?_
    exact ((resIso (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G) n).app _).symm
  have hMP (n : ℤ) : IsZero (tateCohomology (M ⊗ leftRegular ℤ G) n) :=
    (isZero_tensor_indBot ℤ M n).of_iso
      ((tateCohomologyFunctor n).mapIso (whiskerLeftIso M indBotIsoLeftRegular.symm))
  -- Write `u = δ (δ z)` with `z` the class of an integer `m`. Then `u = m • w` for the class `w`
  -- of `δ (δ 1)`, so `m` is prime to `|G|`.
  obtain ⟨y, hy⟩ := exists_eq_δ_δ C u
  obtain ⟨m, hm⟩ : ∃ m : ℤ, H0π (Rep.trivial ℤ G ℤ) y = m • trivialTateHZeroOne G :=
    ⟨y.1, by
      rw [trivialTateHZeroOne_def, ← map_zsmul]
      exact congrArg _ (Subtype.ext (by simp))⟩
  have huw : u = m • ((_root_.TateCohomology.isoGroupCohomology 2).app C).hom
      (_root_.TateCohomology.δ (shortExact_splittingSES C u) 1
        (_root_.TateCohomology.δ shortExact_augSES 0 (trivialTateHZeroOne G))) := by
    refine (Iso.inv_hom_id_apply ((_root_.TateCohomology.isoGroupCohomology 2).app C) u).symm.trans
      ?_
    rw [hy, hm, map_zsmul, map_zsmul, map_zsmul]
  -- Cup product with `u` is `x ↦ δ (δ (x ∪ m))`, a composite of three bijections.
  have := (shortExact_splittingSES C u).epi_g
  have := (shortExact_augSES (G := G)).epi_g
  have Ts := Rep.shortExact_map_tensorLeft_of_leftInverse (shortExact_splittingSES C u).exact M
    (leftInverse_splittingModuleIncl C u)
  have Ta := Rep.shortExact_map_tensorLeft_of_leftInverse shortExact_augSES.exact M
    (exists_leftInverse_augmentationι (k := ℤ) (G := G)).choose_spec
  have hcup (x : tateCohomology M r) :
      cup M C r 2 (r + 1 + 1) h x (((_root_.TateCohomology.isoGroupCohomology 2).app C).inv u) =
        _root_.TateCohomology.δ Ts (r + 1) (_root_.TateCohomology.δ Ta r
          (cupH0 M (Rep.trivial ℤ G ℤ) r x (m • trivialTateHZeroOne G))) := by
    rw [hy, ← hm]
    exact cup_δ_δ M C u x _
  rw [show (fun x ↦ cup M C r 2 (r + 1 + 1) h x
      (((_root_.TateCohomology.isoGroupCohomology 2).app C).inv u)) = _ from funext hcup]
  exact (δ_bijective Ts (r + 1) (hMCu _) (hMCu _)).comp ((δ_bijective Ta r (hMP _) (hMP _)).comp
    (cupH0_zsmul_bijective M (not_dvd_of_eq_zsmul C u hgen hcard huw)))

end TateNakayama

end TauCeti.TateCohomology

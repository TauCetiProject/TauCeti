/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.Modules.Biprod
import TauCeti.AlgebraicGeometry.LineBundle.TwistedSections
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType
import TauCeti.AlgebraicGeometry.Modules.Sheaf

/-!
# Global generation and quotient presentations via ample line bundles

On a scheme `X` with an ample line-bundle class `a` (automatically quasi-compact and
quasi-separated via `IsAmple.compactSpace` and `IsAmple.quasiSeparatedSpace`), twisting any
quasi-coherent `𝒪_X`-module `F` of finite type by sufficiently high powers `aⁿ` yields finite
global generation of `F ⊗ K` for every `K` of class `aⁿ` (EGA II, Prop. 4.5.5; Hartshorne,
Thm. II.5.17; Stacks Tag 01Q3), without Noetherian hypotheses. Specializing to `𝒪_X` globally
generates high ample powers, and dualizing presents `F` as a quotient of finite biproducts of
negative ample twists.

## Main declarations

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_forall_ge_generatingSections`
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_forall_ge_isGloballyGenerated`
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_forall_ge_epi_biproduct`

## References

* A. Grothendieck, *EGA II*, Publ. Math. IHÉS **8** (1961), §4.5.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem II.5.17, Corollary II.5.18.
* [The Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3).
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace TauCeti

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.LineBundleClass

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

private theorem nonempty_tensor_tensorPow_iso (F : X.Modules) (L M : InvertibleSheaf X)
    {d q r n : ℕ} (hM : LineBundleClass.mk M = LineBundleClass.mk L ^ d) (hn : d * q + r = n) :
    Nonempty ((F ⊗ tensorPow (L.obj : X.Modules) r) ⊗ tensorPow (M.obj : X.Modules) q ≅
      F ⊗ tensorPow (L.obj : X.Modules) n) := by
  have hclass : LineBundleClass.mk (InvertibleSheaf.tensorProduct (L.tensorPow r) (M.tensorPow q)) =
      LineBundleClass.mk L ^ n := by
    rw [mk_tensorProduct, mk_tensorPow, mk_tensorPow, hM, ← pow_mul, ← pow_add, add_comm, hn]
  obtain ⟨e⟩ := InvertibleSheaf.nonempty_iso_tensorPow_of_mk_eq hclass
  exact ⟨α_ F _ _ ≪≫ whiskerLeftIso F (tensorIso (L.tensorPowObjIso r).symm
    (M.tensorPowObjIso q).symm ≪≫
    (InvertibleSheaf.tensorProductObjIso (L.tensorPow r) (M.tensorPow q)).symm ≪≫ e)⟩

private theorem exists_finite_span_and_uniform_extension [QuasiSeparatedSpace X] [CompactSpace X]
    (G M : X.Modules) [G.IsQuasicoherent] [G.IsFiniteType] [SheafOfModules.isInvertible X M]
    (s : Γ(M, ⊤)) (hU : IsAffineOpen (M.nonvanishingLocus s)) :
    ∃ (k : ℕ) (g : Fin k → Γ(G, M.nonvanishingLocus s)) (q₀ : ℕ),
      Submodule.span Γ(X, M.nonvanishingLocus s) (Set.range g) = ⊤ ∧
      ∀ q ≥ q₀, ∀ j : Fin k, ∃ t' : Γ(G ⊗ tensorPow M q, ⊤),
        (G ⊗ tensorPow M q).presheaf.map (homOfLE (M.nonvanishingLocus_le s)).op t' =
        tmulRight G (tensorPowSection
          (M.presheaf.map (homOfLE (M.nonvanishingLocus_le s)).op s) q) (g j) := by
  -- Pick finitely many generators of `Γ(G, X_s)` and extend each after twisting by `M^q`.
  have : Module.Finite Γ(X, M.nonvanishingLocus s) Γ(G, M.nonvanishingLocus s) :=
    G.finite_sections_of_isAffineOpen _ hU
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin
    (R := Γ(X, M.nonvanishingLocus s)) (M := Γ(G, M.nonvanishingLocus s))
  choose qj hqj using fun j : Fin k ↦
    exists_forall_ge_exists_map_eq_tmulRight_tensorPowSection G
      (isCompact_univ (X := X)) (isQuasiSeparated_univ (α := X)) s (g j)
  exact ⟨k, g, Finset.univ.sup qj, hg, fun q hq j ↦
    hqj j q ((Finset.le_sup (f := qj) (Finset.mem_univ j)).trans hq)⟩

private theorem span_range_map_eq_top_of_iso_tmulRight {G H M : X.Modules}
    [SheafOfModules.isInvertible X M] (s : Γ(M, ⊤)) {q k : ℕ}
    (g : Fin k → Γ(G, M.nonvanishingLocus s)) (t' : Fin k → Γ(G ⊗ tensorPow M q, ⊤))
    (Φ : G ⊗ tensorPow M q ≅ H)
    (hg : Submodule.span Γ(X, M.nonvanishingLocus s) (Set.range g) = ⊤)
    (ht' : ∀ j, (G ⊗ tensorPow M q).presheaf.map (homOfLE (M.nonvanishingLocus_le s)).op (t' j) =
      tmulRight G (tensorPowSection (M.presheaf.map (homOfLE (M.nonvanishingLocus_le s)).op s) q)
        (g j)) :
    Submodule.span Γ(X, M.nonvanishingLocus s)
      (Set.range fun j ↦ H.presheaf.map (M.nonvanishingLocus s).leTop.op (Φ.hom.app ⊤ (t' j))) =
      ⊤ := by
  let U := M.nonvanishingLocus s
  -- Compose multiplication by `s^q` with `Φ` on sections over `U = X_s`.
  let e : Γ(G, U) ≃ₗ[Γ(X, U)] Γ(H, U) :=
    (LinearEquiv.ofBijective (tmulRight G (tensorPowSection
        (M.presheaf.map (homOfLE (M.nonvanishingLocus_le s)).op s) q))
      (bijective_tmulRight_tensorPowSection_of_le_nonvanishingLocus G _
        (by rw [nonvanishingLocus_map]; exact le_inf le_rfl le_rfl) q)).trans
      (sectionsLinearEquiv Φ U)
  have hmap (j : Fin k) : e (g j) = H.presheaf.map U.leTop.op (Φ.hom.app ⊤ (t' j)) := by
    have hnat : H.presheaf.map U.leTop.op (Φ.hom.app ⊤ (t' j)) =
        Φ.hom.app U ((G ⊗ tensorPow M q).presheaf.map U.leTop.op (t' j)) := by
      simpa only [mapPresheaf_app, unop_op] using
        (Φ.hom.mapPresheaf.naturality_apply U.leTop.op (t' j)).symm
    rw [hnat, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
      sectionsLinearEquiv_apply, ← ht' j]; rfl
  have hrange : (Set.range fun j ↦ H.presheaf.map U.leTop.op (Φ.hom.app ⊤ (t' j))) =
      e.toLinearMap '' Set.range g := by
    rw [← Set.range_comp]; exact congrArg Set.range (funext fun j ↦ (hmap j).symm)
  rw [hrange, ← Submodule.map_span e.toLinearMap, hg, Submodule.map_top, LinearEquiv.range]

private theorem exists_forall_ge_finite_global_span [QuasiSeparatedSpace X] [CompactSpace X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (L M : InvertibleSheaf X)
    {d : ℕ} (hd : 0 < d) (hM : LineBundleClass.mk M = LineBundleClass.mk L ^ d) (s : Γ(M.obj, ⊤))
    (hU : IsAffineOpen (M.obj.nonvanishingLocus s)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ (k : ℕ) (σ : Fin k → Γ(F ⊗ tensorPow (L.obj : X.Modules) n, ⊤)),
        Submodule.span Γ(X, M.obj.nonvanishingLocus s)
          (Set.range fun j ↦ (F ⊗ tensorPow (L.obj : X.Modules) n).presheaf.map
            (M.obj.nonvanishingLocus s).leTop.op (σ j)) = ⊤ := by
  have : (L.obj : X.Modules).IsFiniteType :=
    have : (L.obj : X.Modules).IsFinitePresentation := inferInstance; inferInstance
  -- Step 1: For each residue `r < d`, extend a finite generating set of `Γ(F ⊗ L^r, X_s)`.
  choose k g q₀ hspan hext using fun r : Fin d ↦
    exists_finite_span_and_uniform_extension (F ⊗ tensorPow (L.obj : X.Modules) r) M.obj s hU
  -- Step 2: Divide `n = d * q + r` with `q ≥ sup_r q₀(r)` and transfer generators via `Φ`.
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  refine ⟨d * Finset.univ.sup q₀, fun n hn ↦ ?_⟩
  let r : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  let q : ℕ := n / d
  have hqr : q₀ r ≤ q := (Finset.le_sup (f := q₀) (Finset.mem_univ r)).trans
    ((Nat.le_div_iff_mul_le hd).mpr (by linarith))
  obtain ⟨Φ⟩ := nonempty_tensor_tensorPow_iso F L M hM (Nat.div_add_mod n d)
  choose t' ht' using hext r q hqr
  exact ⟨k r, fun j ↦ Φ.hom.app ⊤ (t' j),
    span_range_map_eq_top_of_iso_tmulRight s (g r) t' Φ (hspan r) ht'⟩

/-- **Serre's global generation theorem** (EGA II, Proposition 4.5.5; Stacks, Tag 01Q3): let `a` be
an ample line-bundle class on a scheme `X` and `F` a quasi-coherent `𝒪_X`-module of finite type.
Some `n₀ : ℕ` ensures that for all `n ≥ n₀` and every `K` of class `aⁿ`, `F ⊗ K` is generated by
finitely many global sections. -/
theorem IsAmple.exists_forall_ge_generatingSections {a : LineBundleClass X} (ha : a.IsAmple)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ K : InvertibleSheaf X, LineBundleClass.mk K = a ^ n →
      ∃ G : (F ⊗ (K.obj : X.Modules)).GeneratingSections, G.IsFiniteType := by
  have := ha.compactSpace; have := ha.quasiSeparatedSpace
  obtain ⟨L, rfl⟩ := mk_surjective a
  choose dx hdx hMx using fun x : X ↦ ha.exists_pos_forall_mk_eq x
  let Mx (x : X) : InvertibleSheaf X := L.tensorPow (dx x)
  choose sx hsx hAffx using fun x : X ↦ hMx x (Mx x) (mk_tensorPow L (dx x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ ((Mx x).obj.nonvanishingLocus (sx x) : Set X))
    (fun x ↦ ((Mx x).obj.nonvanishingLocus (sx x)).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hsx x⟩)
  let U (i : t) : X.Opens := (Mx i).obj.nonvanishingLocus (sx i)
  have hcover : ⨆ i : t, U i = ⊤ := top_unique fun x _ ↦ by
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩
  choose n₀ hn₀ using fun i : t ↦
    exists_forall_ge_finite_global_span F L (Mx i) (hdx i) (mk_tensorPow L (dx i)) (sx i) (hAffx i)
  refine ⟨t.attach.sup n₀, fun n hn K hK ↦ ?_⟩
  choose ki σi hspani using fun i : t ↦
    hn₀ i n ((Finset.le_sup (f := n₀) (Finset.mem_attach t i)).trans hn)
  let σ : (Σ i : t, Fin (ki i)) → Γ(F ⊗ tensorPow (L.obj : X.Modules) n, ⊤) := fun p ↦ σi p.1 p.2
  have hspan (i : t) : Submodule.span Γ(X, U i) (Set.range fun p : Σ i : t, Fin (ki i) ↦
      (F ⊗ tensorPow (L.obj : X.Modules) n).presheaf.map (U i).leTop.op (σ p)) = ⊤ :=
    top_unique (hspani i ▸ Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨⟨i, j⟩, rfl⟩))
  let G₀ := generatingSectionsOfSpanEqTop (F ⊗ tensorPow (L.obj : X.Modules) n)
    (fun i : t ↦ hAffx i) hcover σ hspan
  obtain ⟨e⟩ := InvertibleSheaf.nonempty_iso_tensorPow_of_mk_eq hK
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso
    (toSheafOfModulesIso (whiskerLeftIso F e.symm)) G₀,
    { finite := (inferInstance : G₀.IsFiniteType).finite }⟩

/-- All sufficiently high powers of an ample line-bundle class are globally generated. -/
theorem IsAmple.exists_forall_ge_isGloballyGenerated {a : LineBundleClass X} (ha : a.IsAmple) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ K : InvertibleSheaf X, LineBundleClass.mk K = a ^ n →
      K.IsGloballyGenerated := by
  obtain ⟨n₀, hn₀⟩ := ha.exists_forall_ge_generatingSections (𝟙_ X.Modules)
  refine ⟨n₀, fun n hn K hK ↦
    InvertibleSheaf.isGloballyGenerated_iff_nonempty_generatingSections.mpr ?_⟩
  obtain ⟨G, -⟩ := hn₀ n hn K hK
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso
    (toSheafOfModulesIso (λ_ (K.obj : X.Modules))) G⟩

/-- **Quotient presentation by negative ample twists** (Hartshorne, Corollary II.5.18): for an
ample line-bundle class `a` on a scheme `X` and a quasi-coherent `𝒪_X`-module `F` of finite type,
some `n₀ : ℕ` presents `F` as a quotient of a finite biproduct of copies of `K` whenever `n ≥ n₀`
and `mk K = (aⁿ)⁻¹`. -/
theorem IsAmple.exists_forall_ge_epi_biproduct {a : LineBundleClass X} (ha : a.IsAmple)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ K : InvertibleSheaf X, LineBundleClass.mk K = (a ^ n)⁻¹ →
      ∃ (k : ℕ) (p : (⨁ fun _ : Fin k ↦ (K.obj : X.Modules)) ⟶ F), Epi p := by
  obtain ⟨n₀, hn₀⟩ := ha.exists_forall_ge_generatingSections F
  refine ⟨n₀, fun n hn K hK ↦ ?_⟩
  obtain ⟨P, hP⟩ := mk_surjective (a ^ n)
  obtain ⟨G, hG⟩ := hn₀ n hn P hP
  obtain ⟨e₀⟩ := mk_eq_one_iff.mp (by rw [mk_tensorProduct, hP, hK, mul_inv_cancel] :
    LineBundleClass.mk (InvertibleSheaf.tensorProduct P K) = 1)
  exact exists_epi_biproduct_of_generatingSections
    ((InvertibleSheaf.tensorProductObjIso P K).symm ≪≫ isoOfSheafIso X e₀) G

end TauCeti.AlgebraicGeometry.LineBundleClass

end
